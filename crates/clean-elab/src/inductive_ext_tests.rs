// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended inductive type elaboration (`inductive_ext`).

use clean_kernel::{BinderInfo, Expr, Level, Name};

use crate::inductive_ext::{
    check_strict_positivity, compute_rec_args, infer_inductive_universe, ConstructorSpec,
    InductiveElabConfig, InductiveResult, InductiveSpec, MutualInductiveResult,
    MutualInductiveSpec, PositivityError, PositivityViolation,
};
use crate::inductive_ext_elab::{elaborate_inductive, elaborate_mutual_inductive_spec};

// =============================================================================
// Test helpers
// =============================================================================

/// Sort 1 (Type 0).
fn type_0() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// Sort 0 (Prop).
fn prop() -> Expr {
    Expr::sort(Level::zero())
}

/// Non-dependent arrow: `domain -> codomain`.
fn arrow(domain: Expr, codomain: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, codomain)
}

/// Build a minimal inductive spec for a type with given name and type former.
fn simple_spec(name: &str, type_: Expr) -> InductiveSpec {
    InductiveSpec {
        name: Name::from_string(name),
        params: Vec::new(),
        indices: Vec::new(),
        type_,
        ctors: Vec::new(),
        is_recursive: false,
        is_nested: false,
    }
}

/// Build a constructor spec with no fields.
fn nullary_ctor(name: &str, type_: Expr) -> ConstructorSpec {
    ConstructorSpec {
        name: Name::from_string(name),
        fields: Vec::new(),
        type_,
    }
}

/// Build a constructor spec with one field.
fn unary_ctor(
    name: &str,
    field_name: &str,
    field_ty: Expr,
    is_recursive: bool,
    type_: Expr,
) -> ConstructorSpec {
    ConstructorSpec {
        name: Name::from_string(name),
        fields: vec![(Name::from_string(field_name), field_ty, is_recursive)],
        type_,
    }
}

// =============================================================================
// Config tests
// =============================================================================

#[test]
fn test_config_default_values() {
    let config = InductiveElabConfig::default();
    assert!(config.check_positivity);
    assert!(config.allow_nested);
    assert!(config.allow_mutual);
    assert_eq!(config.max_params, 16);
}

#[test]
fn test_config_custom_values() {
    let config = InductiveElabConfig {
        check_positivity: false,
        allow_nested: false,
        allow_mutual: false,
        max_params: 4,
    };
    assert!(!config.check_positivity);
    assert!(!config.allow_nested);
    assert!(!config.allow_mutual);
    assert_eq!(config.max_params, 4);
}

// =============================================================================
// Positivity checking tests
// =============================================================================

#[test]
fn test_positivity_empty_constructors_passes() {
    let spec = simple_spec("Empty", type_0());
    check_strict_positivity(&spec).expect("no constructors should pass positivity");
}

#[test]
fn test_positivity_nullary_constructor_passes() {
    let nat_name = Name::from_string("Nat");
    let nat_const = Expr::const_(nat_name.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const));
    check_strict_positivity(&spec).expect("nullary ctor should pass");
}

#[test]
fn test_positivity_simple_recursive_passes() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));
    check_strict_positivity(&spec).expect("Nat.succ : Nat -> Nat should be positive");
}

#[test]
fn test_positivity_negative_occurrence_fails() {
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");
    let neg_field_ty = arrow(bad_const.clone(), bool_const.clone());

    let mut spec = simple_spec("Bad", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Bad.mk"),
        fields: vec![(Name::from_string("f"), neg_field_ty.clone(), false)],
        type_: arrow(neg_field_ty, bad_const),
    });

    let err = check_strict_positivity(&spec).unwrap_err();
    assert_eq!(err.ctor, Name::from_string("Bad.mk"));
    assert_eq!(err.param_index, 0);
    assert_eq!(err.violation, PositivityViolation::NegativeOccurrence);
}

#[test]
fn test_positivity_deep_negative_fails() {
    // (X -> Bad -> Bool) -> Bad
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let x_const = Expr::const_str("X");
    let bool_const = Expr::const_str("Bool");
    // Inner: Bad -> Bool
    let inner = arrow(bad_const.clone(), bool_const);
    // Outer domain: X -> (Bad -> Bool)
    let domain = arrow(x_const, inner);

    let mut spec = simple_spec("Bad", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Bad.mk"),
        fields: vec![(Name::from_string("f"), domain.clone(), false)],
        type_: arrow(domain, bad_const),
    });

    let err = check_strict_positivity(&spec).unwrap_err();
    assert_eq!(err.violation, PositivityViolation::NegativeOccurrence);
}

#[test]
fn test_positivity_multiple_ctors_second_fails() {
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");

    let mut spec = simple_spec("Bad", type_0());
    // First ctor is fine
    spec.ctors.push(nullary_ctor("Bad.ok", bad_const.clone()));
    // Second ctor has negative occurrence
    let neg_ty = arrow(bad_const.clone(), bool_const);
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Bad.bad"),
        fields: vec![(Name::from_string("f"), neg_ty.clone(), false)],
        type_: arrow(neg_ty, bad_const),
    });

    let err = check_strict_positivity(&spec).unwrap_err();
    assert_eq!(err.ctor, Name::from_string("Bad.bad"));
}

#[test]
fn test_positivity_positive_in_codomain_passes() {
    // (Bool -> Nat) -> Nat  — Nat only in positive (codomain) positions
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");
    let field_ty = arrow(bool_const, nat_const.clone());

    let mut spec = simple_spec("Nat", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Nat.mk"),
        fields: vec![(Name::from_string("f"), field_ty.clone(), false)],
        type_: arrow(field_ty, nat_const),
    });

    // This should fail because field_ty itself contains Nat in codomain of arrow,
    // but the field type `(Bool -> Nat)` when analyzed for negativity of Nat:
    // the Pi domain is Bool (no mention of Nat), body is Nat (positive).
    // So this should pass.
    check_strict_positivity(&spec).expect("Nat in codomain only should pass");
}

#[test]
fn test_positivity_error_display() {
    let err = PositivityError {
        ctor: Name::from_string("Bad.mk"),
        param_index: 2,
        violation: PositivityViolation::NegativeOccurrence,
    };
    let msg = err.to_string();
    assert!(msg.contains("Bad.mk"), "should mention constructor: {msg}");
    assert!(
        msg.contains("negative"),
        "should mention violation type: {msg}"
    );
    assert!(msg.contains("2"), "should mention param index: {msg}");
}

#[test]
fn test_positivity_violation_enum_equality() {
    assert_eq!(
        PositivityViolation::NegativeOccurrence,
        PositivityViolation::NegativeOccurrence
    );
    assert_ne!(
        PositivityViolation::NegativeOccurrence,
        PositivityViolation::NonStrictlyPositive
    );
    assert_ne!(
        PositivityViolation::NonStrictlyPositive,
        PositivityViolation::InNestedNonPositive
    );
}

// =============================================================================
// Recursive arg computation tests
// =============================================================================

#[test]
fn test_rec_args_empty_ctors() {
    let spec = simple_spec("Empty", type_0());
    let args = compute_rec_args(&spec);
    assert!(args.is_empty());
}

#[test]
fn test_rec_args_nullary_ctor() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const));
    let args = compute_rec_args(&spec);
    assert!(args.is_empty(), "nullary ctor has no rec args");
}

#[test]
fn test_rec_args_one_recursive_field() {
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));
    let args = compute_rec_args(&spec);
    assert_eq!(args, vec![0], "succ's first field is recursive");
}

#[test]
fn test_rec_args_mixed_fields() {
    let tree = Name::from_string("Tree");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let nat_const = Expr::const_str("Nat");
    let mut spec = simple_spec("Tree", type_0());
    spec.is_recursive = true;
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Tree.node"),
        fields: vec![
            (Name::from_string("val"), nat_const, false),
            (Name::from_string("left"), tree_const.clone(), true),
            (Name::from_string("right"), tree_const.clone(), true),
        ],
        type_: arrow(
            Expr::const_str("Nat"),
            arrow(tree_const.clone(), arrow(tree_const.clone(), tree_const)),
        ),
    });
    let args = compute_rec_args(&spec);
    assert_eq!(args, vec![1, 2], "left(1) and right(2) are recursive");
}

// =============================================================================
// Universe inference tests
// =============================================================================

#[test]
fn test_infer_universe_no_ctors() {
    let level = infer_inductive_universe(&[], &[]);
    assert_eq!(level, Level::zero());
}

#[test]
fn test_infer_universe_simple_type_field() {
    let ctors = vec![ConstructorSpec {
        name: Name::from_string("Wrap.mk"),
        fields: vec![(Name::from_string("val"), type_0(), false)],
        type_: arrow(type_0(), Expr::const_str("Wrap")),
    }];
    let level = infer_inductive_universe(&[], &ctors);
    // imax(0, succ(0)) = succ(0) = 1
    assert_eq!(
        level,
        Level::imax(Level::zero(), Level::succ(Level::zero()))
    );
}

#[test]
fn test_infer_universe_prop_field() {
    let ctors = vec![ConstructorSpec {
        name: Name::from_string("P.mk"),
        fields: vec![(Name::from_string("pf"), prop(), false)],
        type_: arrow(prop(), Expr::const_str("P")),
    }];
    let level = infer_inductive_universe(&[], &ctors);
    // imax(0, 0) = 0
    assert_eq!(level, Level::imax(Level::zero(), Level::zero()));
}

#[test]
fn test_infer_universe_with_params() {
    let params = vec![(Name::from_string("A"), type_0())];
    let ctors = vec![ConstructorSpec {
        name: Name::from_string("Box.mk"),
        fields: vec![(Name::from_string("val"), Expr::const_str("A"), false)],
        type_: Expr::const_str("Box"),
    }];
    let level = infer_inductive_universe(&params, &ctors);
    // The level accounts for both field type and param type
    // imax(imax(0, 0), succ(0))
    let inner = Level::imax(Level::zero(), Level::zero());
    let expected = Level::imax(inner, Level::succ(Level::zero()));
    assert_eq!(level, expected);
}

#[test]
fn test_infer_universe_multiple_fields() {
    let ctors = vec![ConstructorSpec {
        name: Name::from_string("Pair.mk"),
        fields: vec![
            (Name::from_string("fst"), type_0(), false),
            (Name::from_string("snd"), prop(), false),
        ],
        type_: Expr::const_str("Pair"),
    }];
    let level = infer_inductive_universe(&[], &ctors);
    // imax(imax(0, succ(0)), 0) = imax(succ(0), 0)
    let inner = Level::imax(Level::zero(), Level::succ(Level::zero()));
    let expected = Level::imax(inner, Level::zero());
    assert_eq!(level, expected);
}

// =============================================================================
// Single inductive elaboration tests
// =============================================================================

#[test]
fn test_elaborate_empty_type() {
    let config = InductiveElabConfig::default();
    let spec = simple_spec("Empty", type_0());
    let result = elaborate_inductive(&spec, &config).expect("empty type should elaborate");
    assert!(result.cases_on.is_none(), "no ctors => no casesOn");
    assert!(result.no_confusion.is_none(), "no ctors => no noConfusion");
}

#[test]
fn test_elaborate_unit_type() {
    let config = InductiveElabConfig::default();
    let unit_const = Expr::const_str("Unit");
    let mut spec = simple_spec("Unit", type_0());
    spec.ctors.push(nullary_ctor("Unit.unit", unit_const));
    let result = elaborate_inductive(&spec, &config).expect("Unit should elaborate");
    assert!(result.cases_on.is_some(), "Unit has ctors => casesOn");
    assert!(result.no_confusion.is_some(), "non-Prop => noConfusion");
}

#[test]
fn test_elaborate_prop_type_no_confusion() {
    let config = InductiveElabConfig::default();
    let true_const = Expr::const_str("True");
    let mut spec = simple_spec("True", prop());
    spec.ctors.push(nullary_ctor("True.intro", true_const));
    let result = elaborate_inductive(&spec, &config).expect("True should elaborate");
    assert!(result.cases_on.is_some(), "True has ctors => casesOn");
    assert!(result.no_confusion.is_none(), "Prop type => no noConfusion");
}

#[test]
fn test_elaborate_nat_type() {
    let config = InductiveElabConfig::default();
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);

    let mut spec = simple_spec("Nat", type_0());
    spec.is_recursive = true;
    spec.ctors.push(nullary_ctor("Nat.zero", nat_const.clone()));
    spec.ctors.push(unary_ctor(
        "Nat.succ",
        "pred",
        nat_const.clone(),
        true,
        arrow(nat_const.clone(), nat_const),
    ));

    let result = elaborate_inductive(&spec, &config).expect("Nat should elaborate");
    assert!(result.cases_on.is_some());
    assert!(result.no_confusion.is_some());
}

#[test]
fn test_elaborate_exceeds_max_params() {
    let config = InductiveElabConfig {
        max_params: 2,
        ..Default::default()
    };
    let mut spec = simple_spec("Big", type_0());
    spec.params = vec![
        (Name::from_string("A"), type_0()),
        (Name::from_string("B"), type_0()),
        (Name::from_string("C"), type_0()),
    ];

    let result = elaborate_inductive(&spec, &config);
    assert!(result.is_err(), "exceeding max_params should fail");
}

#[test]
fn test_elaborate_nested_rejected_when_disabled() {
    let config = InductiveElabConfig {
        allow_nested: false,
        ..Default::default()
    };
    let mut spec = simple_spec("T", type_0());
    spec.is_nested = true;

    let result = elaborate_inductive(&spec, &config);
    assert!(result.is_err(), "nested should be rejected when disabled");
}

#[test]
fn test_elaborate_nested_allowed_when_enabled() {
    let config = InductiveElabConfig::default();
    let t_const = Expr::const_str("T");
    let mut spec = simple_spec("T", type_0());
    spec.is_nested = true;
    spec.ctors.push(nullary_ctor("T.mk", t_const));

    let result = elaborate_inductive(&spec, &config);
    assert!(result.is_ok(), "nested should pass when enabled");
}

#[test]
fn test_elaborate_positivity_disabled_accepts_negative() {
    let config = InductiveElabConfig {
        check_positivity: false,
        ..Default::default()
    };
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");
    let neg_ty = arrow(bad_const.clone(), bool_const);

    let mut spec = simple_spec("Bad", type_0());
    spec.ctors.push(ConstructorSpec {
        name: Name::from_string("Bad.mk"),
        fields: vec![(Name::from_string("f"), neg_ty.clone(), false)],
        type_: arrow(neg_ty, bad_const),
    });

    let result = elaborate_inductive(&spec, &config);
    assert!(
        result.is_ok(),
        "non-positive should pass with check disabled"
    );
}

// =============================================================================
// Mutual inductive elaboration tests
// =============================================================================

#[test]
fn test_elaborate_mutual_simple() {
    let config = InductiveElabConfig::default();
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);

    let spec = MutualInductiveSpec {
        inductives: vec![
            {
                let mut s = simple_spec("Tree", type_0());
                s.is_recursive = true;
                s.ctors.push(unary_ctor(
                    "Tree.node",
                    "children",
                    forest_const.clone(),
                    true,
                    arrow(forest_const.clone(), tree_const.clone()),
                ));
                s
            },
            {
                let mut s = simple_spec("Forest", type_0());
                s.is_recursive = true;
                s.ctors
                    .push(nullary_ctor("Forest.nil", forest_const.clone()));
                s.ctors.push(ConstructorSpec {
                    name: Name::from_string("Forest.cons"),
                    fields: vec![
                        (Name::from_string("head"), tree_const.clone(), true),
                        (Name::from_string("tail"), forest_const.clone(), true),
                    ],
                    type_: arrow(tree_const, arrow(forest_const.clone(), forest_const)),
                });
                s
            },
        ],
        universe_params: vec![Name::from_string("u")],
    };

    let result = elaborate_mutual_inductive_spec(&spec, &config)
        .expect("tree/forest mutual should elaborate");
    assert_eq!(result.results.len(), 2);
    assert!(result.mutual_recursors.len() >= 2);

    // Both should have casesOn
    assert!(result.results[0].cases_on.is_some());
    assert!(result.results[1].cases_on.is_some());
}

#[test]
fn test_elaborate_mutual_rejected_when_disabled() {
    let config = InductiveElabConfig {
        allow_mutual: false,
        ..Default::default()
    };

    let spec = MutualInductiveSpec {
        inductives: vec![simple_spec("A", type_0()), simple_spec("B", type_0())],
        universe_params: Vec::new(),
    };

    let result = elaborate_mutual_inductive_spec(&spec, &config);
    assert!(result.is_err(), "mutual should be rejected when disabled");
}

#[test]
fn test_elaborate_mutual_duplicate_names_rejected() {
    let config = InductiveElabConfig::default();
    let spec = MutualInductiveSpec {
        inductives: vec![simple_spec("Same", type_0()), simple_spec("Same", type_0())],
        universe_params: Vec::new(),
    };

    let result = elaborate_mutual_inductive_spec(&spec, &config);
    assert!(result.is_err(), "duplicate names should be rejected");
}

#[test]
fn test_elaborate_mutual_single_type_allowed() {
    let config = InductiveElabConfig {
        allow_mutual: false,
        ..Default::default()
    };

    let nat_const = Expr::const_str("Nat");
    let mut nat_spec = simple_spec("Nat", type_0());
    nat_spec.ctors.push(nullary_ctor("Nat.zero", nat_const));

    let spec = MutualInductiveSpec {
        inductives: vec![nat_spec],
        universe_params: Vec::new(),
    };

    let result = elaborate_mutual_inductive_spec(&spec, &config);
    assert!(
        result.is_ok(),
        "single type should pass even with allow_mutual=false"
    );
}

#[test]
fn test_elaborate_mutual_param_limit() {
    let config = InductiveElabConfig {
        max_params: 1,
        ..Default::default()
    };

    let mut spec_a = simple_spec("A", type_0());
    spec_a.params = vec![
        (Name::from_string("X"), type_0()),
        (Name::from_string("Y"), type_0()),
    ];

    let spec = MutualInductiveSpec {
        inductives: vec![spec_a],
        universe_params: Vec::new(),
    };

    let result = elaborate_mutual_inductive_spec(&spec, &config);
    assert!(result.is_err(), "exceeding max_params should fail");
}

// =============================================================================
// Edge case tests
// =============================================================================

#[test]
fn test_spec_clone() {
    let spec = simple_spec("T", type_0());
    let cloned = spec.clone();
    assert_eq!(spec.name, cloned.name);
}

#[test]
fn test_ctor_spec_clone() {
    let cs = nullary_ctor("T.mk", Expr::const_str("T"));
    let cloned = cs.clone();
    assert_eq!(cs.name, cloned.name);
}

#[test]
fn test_inductive_result_has_all_fields() {
    let result = InductiveResult {
        decl: type_0(),
        recursor: type_0(),
        cases_on: Some(type_0()),
        no_confusion: Some(type_0()),
    };
    assert!(result.cases_on.is_some());
    assert!(result.no_confusion.is_some());
}

#[test]
fn test_mutual_inductive_result_empty() {
    let result = MutualInductiveResult {
        results: Vec::new(),
        mutual_recursors: Vec::new(),
    };
    assert!(result.results.is_empty());
    assert!(result.mutual_recursors.is_empty());
}

#[test]
fn test_positivity_error_clone() {
    let err = PositivityError {
        ctor: Name::from_string("X.mk"),
        param_index: 0,
        violation: PositivityViolation::NegativeOccurrence,
    };
    let cloned = err.clone();
    assert_eq!(err, cloned);
}

#[test]
fn test_elaborate_indexed_family_no_indices() {
    let config = InductiveElabConfig::default();
    let mut spec = simple_spec("Vec", type_0());
    // Vec with one param (A : Type) but no index yet
    spec.params = vec![(Name::from_string("A"), type_0())];
    spec.ctors
        .push(nullary_ctor("Vec.nil", Expr::const_str("Vec")));
    let result = elaborate_inductive(&spec, &config);
    assert!(result.is_ok());
}

#[test]
fn test_elaborate_indexed_family_with_index() {
    let config = InductiveElabConfig::default();
    let mut spec = simple_spec("Vec", arrow(Expr::const_str("Nat"), type_0()));
    spec.params = vec![(Name::from_string("A"), type_0())];
    spec.indices = vec![(Name::from_string("n"), Expr::const_str("Nat"))];
    spec.ctors
        .push(nullary_ctor("Vec.nil", Expr::const_str("Vec")));
    let result = elaborate_inductive(&spec, &config);
    assert!(result.is_ok());
}
