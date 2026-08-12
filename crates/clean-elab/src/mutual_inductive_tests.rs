// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for mutual inductive type elaboration.

use super::*;
use clean_kernel::{BinderInfo, Constructor, Environment, Expr, Level, Name};

// ─────────────────────────────────────────────────────────────────────────────
// Test helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Create a simple `Sort u` type where u is Level::succ(Level::zero()) = Type 0.
fn type_0() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// Create Prop (Sort 0).
fn prop() -> Expr {
    Expr::sort(Level::zero())
}

/// Create `Sort (u + 1)` for a universe param.
// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn type_param(name: &str) -> Expr {
    Expr::sort(Level::succ(Level::param(Name::from_string(name))))
}

/// Build a simple inductive type info with no constructors.
fn simple_type(name: &str) -> InductiveTypeInfo {
    InductiveTypeInfo {
        name: Name::from_string(name),
        type_expr: type_0(),
        constructors: Vec::new(),
        is_recursive: false,
        references_siblings: false,
    }
}

/// Build a constructor info.
fn ctor(name: &str, type_expr: Expr) -> ConstructorInfo {
    ConstructorInfo {
        name: Name::from_string(name),
        type_expr,
    }
}

/// Build a simple mutual block with the given types.
fn make_block(types: Vec<InductiveTypeInfo>) -> MutualInductiveBlock {
    MutualInductiveBlock {
        types,
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    }
}

/// Build a simple arrow type: `domain -> codomain` (non-dependent Pi).
fn arrow(domain: Expr, codomain: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, codomain)
}

// ─────────────────────────────────────────────────────────────────────────────
// Validation tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_validate_empty_block_fails() {
    let block = make_block(Vec::new());
    let config = MutualIndConfig::default();
    let result = validate_mutual_block(&block, &config);
    assert!(result.is_err(), "empty block should fail validation");
}

#[test]
fn test_validate_single_type_passes() {
    let block = make_block(vec![simple_type("Nat")]);
    let config = MutualIndConfig::default();
    validate_mutual_block(&block, &config).expect("single type should pass");
}

#[test]
fn test_validate_two_mutual_types_passes() {
    let block = make_block(vec![simple_type("Tree"), simple_type("Forest")]);
    let config = MutualIndConfig::default();
    validate_mutual_block(&block, &config).expect("two types should pass");
}

#[test]
fn test_validate_three_mutual_types_passes() {
    let block = make_block(vec![simple_type("A"), simple_type("B"), simple_type("C")]);
    let config = MutualIndConfig::default();
    validate_mutual_block(&block, &config).expect("three types should pass");
}

#[test]
fn test_validate_duplicate_type_names_fails() {
    let block = make_block(vec![simple_type("Nat"), simple_type("Nat")]);
    let config = MutualIndConfig::default();
    let result = validate_mutual_block(&block, &config);
    assert!(result.is_err(), "duplicate type names should fail");
}

#[test]
fn test_validate_duplicate_constructor_names_fails() {
    let mut ty1 = simple_type("A");
    ty1.constructors.push(ctor("mk", type_0()));
    let mut ty2 = simple_type("B");
    ty2.constructors.push(ctor("mk", type_0()));

    let block = make_block(vec![ty1, ty2]);
    let config = MutualIndConfig::default();
    let result = validate_mutual_block(&block, &config);
    assert!(result.is_err(), "duplicate ctor names should fail");
}

#[test]
fn test_validate_exceeds_max_types_fails() {
    let types: Vec<InductiveTypeInfo> = (0..33).map(|i| simple_type(&format!("T{i}"))).collect();
    let block = make_block(types);
    let config = MutualIndConfig::default();
    let result = validate_mutual_block(&block, &config);
    assert!(result.is_err(), "exceeding max types should fail");
}

#[test]
fn test_validate_custom_max_types() {
    let types: Vec<InductiveTypeInfo> = (0..5).map(|i| simple_type(&format!("T{i}"))).collect();
    let block = make_block(types);
    let config = MutualIndConfig {
        max_mutual_types: 3,
        ..Default::default()
    };
    let result = validate_mutual_block(&block, &config);
    assert!(result.is_err(), "5 types with max=3 should fail");
}

// ─────────────────────────────────────────────────────────────────────────────
// Positivity tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_positivity_no_constructors_passes() {
    let name = Name::from_string("Empty");
    let result = check_strict_positivity(&name, &[], &[&name], 0);
    assert_eq!(result, PositivityResult::StrictlyPositive);
}

#[test]
fn test_positivity_simple_constructor_passes() {
    // Nat.succ : Nat -> Nat
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    let ctor_type = arrow(nat_const.clone(), nat_const);
    let ctors = vec![Constructor {
        name: Name::from_string("Nat.succ"),
        type_: ctor_type,
    }];
    let result = check_strict_positivity(&nat, &ctors, &[&nat], 0);
    assert_eq!(result, PositivityResult::StrictlyPositive);
}

#[test]
fn test_positivity_non_positive_fails() {
    // Bad constructor: (Nat -> Bool) -> Nat
    // Nat appears to the left of an arrow within the domain.
    let nat = Name::from_string("Nat");
    let bool_const = Expr::const_str("Bool");
    let nat_const = Expr::const_(nat.clone(), vec![]);
    // Domain: Nat -> Bool (Nat is in negative position)
    let bad_domain = arrow(nat_const.clone(), bool_const);
    let ctor_type = arrow(bad_domain, nat_const);
    let ctors = vec![Constructor {
        name: Name::from_string("Bad.mk"),
        type_: ctor_type,
    }];
    let result = check_strict_positivity(&nat, &ctors, &[&nat], 0);
    assert!(
        matches!(result, PositivityResult::NonPositive { .. }),
        "non-positive occurrence should be detected"
    );
}

#[test]
fn test_positivity_mutual_cross_reference_positive() {
    // Tree.node : Forest -> Tree
    // Forest.cons : Tree -> Forest -> Forest
    // Both are strictly positive.
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);

    let tree_ctors = vec![Constructor {
        name: Name::from_string("Tree.node"),
        type_: arrow(forest_const.clone(), tree_const.clone()),
    }];
    let forest_ctors = vec![Constructor {
        name: Name::from_string("Forest.cons"),
        type_: arrow(
            tree_const.clone(),
            arrow(forest_const.clone(), forest_const.clone()),
        ),
    }];

    let all_names = [&tree, &forest];
    let r1 = check_strict_positivity(&tree, &tree_ctors, &all_names, 0);
    assert_eq!(r1, PositivityResult::StrictlyPositive);

    let r2 = check_strict_positivity(&forest, &forest_ctors, &all_names, 0);
    assert_eq!(r2, PositivityResult::StrictlyPositive);
}

#[test]
fn test_positivity_mutual_non_positive_cross_ref() {
    // Bad: Tree.bad : (Forest -> Bool) -> Tree
    // Forest appears negatively in Tree's constructor.
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");

    let bad_domain = arrow(forest_const, bool_const);
    let tree_ctors = vec![Constructor {
        name: Name::from_string("Tree.bad"),
        type_: arrow(bad_domain, tree_const),
    }];

    let all_names = [&tree, &forest];
    let r = check_strict_positivity(&tree, &tree_ctors, &all_names, 0);
    // The kernel detects that `Forest -> Bool` puts Forest in a
    // negative position even when `inductive_name == Tree` is the
    // currently-checked type (Wave 107). The Lean 4 reference
    // (`is_valid_ind_app` / `check_positivity`) walks every mutual name
    // at the strict-positivity check, and the elaborator-side
    // `check_mutual_positivity` (which the kernel-level checker
    // mirrors) calls into the same routine for every mutual sibling.
    assert!(
        matches!(r, PositivityResult::NonPositive { .. }),
        "the checker must reject Tree.bad : (Forest -> Bool) -> Tree as non-positive"
    );
}

#[test]
fn test_positivity_mutual_strictly_positive_arg_not_rejected() {
    // Negative for Wave 107: `Tree.node : Forest -> Tree` must continue
    // to be accepted — `Forest` appears as a top-level Pi argument
    // (strictly-positive position), not under an inner arrow. The
    // sibling-walking strict-positivity refinement must not collapse
    // arguments-of-the-constructor with arguments-of-a-nested-arrow.
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);

    let tree_ctors = vec![Constructor {
        name: Name::from_string("Tree.node"),
        type_: arrow(forest_const.clone(), tree_const.clone()),
    }];

    let all_names = [&tree, &forest];
    let r = check_strict_positivity(&tree, &tree_ctors, &all_names, 0);
    assert_eq!(
        r,
        PositivityResult::StrictlyPositive,
        "Tree.node : Forest -> Tree must be accepted (strictly positive)"
    );
}

#[test]
fn test_check_all_positivity_passes() {
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);

    let block = MutualInductiveBlock {
        types: vec![
            InductiveTypeInfo {
                name: tree.clone(),
                type_expr: type_0(),
                constructors: vec![ctor(
                    "Tree.node",
                    arrow(forest_const.clone(), tree_const.clone()),
                )],
                is_recursive: true,
                references_siblings: true,
            },
            InductiveTypeInfo {
                name: forest.clone(),
                type_expr: type_0(),
                constructors: vec![
                    ctor("Forest.nil", forest_const.clone()),
                    ctor(
                        "Forest.cons",
                        arrow(tree_const, arrow(forest_const.clone(), forest_const)),
                    ),
                ],
                is_recursive: true,
                references_siblings: true,
            },
        ],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    check_all_positivity(&block).expect("tree/forest should be strictly positive");
}

// ─────────────────────────────────────────────────────────────────────────────
// Universe computation tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_universe_empty_returns_zero() {
    let level = compute_result_universe(&[]);
    assert_eq!(level, Level::zero());
}

#[test]
fn test_universe_single_type() {
    let types = vec![InductiveTypeInfo {
        name: Name::from_string("Nat"),
        type_expr: type_0(),
        constructors: Vec::new(),
        is_recursive: false,
        references_siblings: false,
    }];
    let level = compute_result_universe(&types);
    assert_eq!(level, Level::succ(Level::zero()));
}

#[test]
fn test_universe_two_types_max() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let types = vec![
        InductiveTypeInfo {
            name: Name::from_string("A"),
            type_expr: Expr::sort(u.clone()),
            constructors: Vec::new(),
            is_recursive: false,
            references_siblings: false,
        },
        InductiveTypeInfo {
            name: Name::from_string("B"),
            type_expr: Expr::sort(v.clone()),
            constructors: Vec::new(),
            is_recursive: false,
            references_siblings: false,
        },
    ];
    let level = compute_result_universe(&types);
    assert_eq!(level, Level::max(u, v));
}

#[test]
fn test_universe_prop_type() {
    let types = vec![InductiveTypeInfo {
        name: Name::from_string("P"),
        type_expr: prop(),
        constructors: Vec::new(),
        is_recursive: false,
        references_siblings: false,
    }];
    let level = compute_result_universe(&types);
    assert_eq!(level, Level::zero());
}

#[test]
fn test_universe_pi_telescope_type() {
    // Type: (A : Type) -> Type 1
    let inner = Expr::sort(Level::succ(Level::succ(Level::zero())));
    let telescope = Expr::pi(BinderInfo::Default, type_0(), inner);
    let types = vec![InductiveTypeInfo {
        name: Name::from_string("F"),
        type_expr: telescope,
        constructors: Vec::new(),
        is_recursive: false,
        references_siblings: false,
    }];
    let level = compute_result_universe(&types);
    // Should extract Sort 2 from the return type of the Pi.
    assert_eq!(level, Level::succ(Level::succ(Level::zero())));
}

// ─────────────────────────────────────────────────────────────────────────────
// Large elimination tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_large_elim_empty_block() {
    let env = Environment::new();
    let block = make_block(Vec::new());
    assert!(!can_eliminate_to_type(&block, &env));
}

#[test]
fn test_large_elim_single_type_in_type() {
    let env = Environment::new();
    let block = make_block(vec![simple_type("Nat")]);
    // Non-prop type with no constructors allows large elim.
    assert!(can_eliminate_to_type(&block, &env));
}

#[test]
fn test_large_elim_mutual_prop_denied() {
    let env = Environment::new();
    let mut ty1 = simple_type("A");
    ty1.type_expr = prop();
    let mut ty2 = simple_type("B");
    ty2.type_expr = prop();
    let block = make_block(vec![ty1, ty2]);
    // Mutual Prop inductives never allow large elimination.
    assert!(!can_eliminate_to_type(&block, &env));
}

#[test]
fn test_large_elim_mutual_type_allowed() {
    let env = Environment::new();
    let block = make_block(vec![simple_type("Tree"), simple_type("Forest")]);
    assert!(can_eliminate_to_type(&block, &env));
}

// ─────────────────────────────────────────────────────────────────────────────
// Recursor generation tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_recursor_single_type_basic() {
    let env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);

    let mut ty = simple_type("Nat");
    ty.constructors = vec![
        ctor("Nat.zero", nat_const.clone()),
        ctor("Nat.succ", arrow(nat_const.clone(), nat_const)),
    ];
    let block = make_block(vec![ty]);

    let specs = generate_mutual_recursors(&block, &env);
    assert_eq!(specs.len(), 1, "should generate one recursor");

    let rec = &specs[0].val;
    assert_eq!(rec.name, Name::from_string("Nat.rec"));
    assert_eq!(rec.inductive_name, Name::from_string("Nat"));
    assert_eq!(rec.num_motives, 1);
    assert_eq!(rec.num_minors, 2); // zero + succ
    assert_eq!(rec.rules.len(), 2);
}

#[test]
fn test_recursor_mutual_block() {
    let env = Environment::new();
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);

    let block = MutualInductiveBlock {
        types: vec![
            InductiveTypeInfo {
                name: tree.clone(),
                type_expr: type_0(),
                constructors: vec![ctor(
                    "Tree.node",
                    arrow(forest_const.clone(), tree_const.clone()),
                )],
                is_recursive: true,
                references_siblings: true,
            },
            InductiveTypeInfo {
                name: forest.clone(),
                type_expr: type_0(),
                constructors: vec![
                    ctor("Forest.nil", forest_const.clone()),
                    ctor(
                        "Forest.cons",
                        arrow(tree_const, arrow(forest_const.clone(), forest_const)),
                    ),
                ],
                is_recursive: true,
                references_siblings: true,
            },
        ],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    let specs = generate_mutual_recursors(&block, &env);
    assert_eq!(specs.len(), 2, "should generate two recursors");

    // Tree.rec
    let tree_rec = &specs[0].val;
    assert_eq!(tree_rec.name, Name::from_string("Tree.rec"));
    assert_eq!(tree_rec.num_motives, 2); // motives for Tree and Forest
    assert_eq!(tree_rec.num_minors, 3); // node + nil + cons
    assert_eq!(tree_rec.rules.len(), 1); // only Tree's constructors

    // Forest.rec
    let forest_rec = &specs[1].val;
    assert_eq!(forest_rec.name, Name::from_string("Forest.rec"));
    assert_eq!(forest_rec.num_motives, 2);
    assert_eq!(forest_rec.num_minors, 3);
    assert_eq!(forest_rec.rules.len(), 2); // nil + cons
}

#[test]
fn test_recursor_recursive_fields() {
    let env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);

    let mut ty = simple_type("Nat");
    ty.constructors = vec![
        ctor("Nat.zero", nat_const.clone()),
        ctor("Nat.succ", arrow(nat_const.clone(), nat_const)),
    ];
    let block = make_block(vec![ty]);

    let specs = generate_mutual_recursors(&block, &env);
    let rec = &specs[0].val;

    // zero has 0 fields
    assert_eq!(rec.rules[0].num_fields, 0);
    assert!(rec.rules[0].recursive_fields.is_empty());

    // succ has 1 field, and it's recursive (Nat -> Nat)
    assert_eq!(rec.rules[1].num_fields, 1);
    assert_eq!(rec.rules[1].recursive_fields, vec![true]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Full pipeline tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_elaborate_single_inductive() {
    let env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_const = Expr::const_(nat.clone(), vec![]);

    let block = MutualInductiveBlock {
        types: vec![InductiveTypeInfo {
            name: nat.clone(),
            type_expr: type_0(),
            constructors: vec![
                ctor("Nat.zero", nat_const.clone()),
                ctor("Nat.succ", arrow(nat_const.clone(), nat_const)),
            ],
            is_recursive: true,
            references_siblings: false,
        }],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    let config = MutualIndConfig::default();
    let result = elaborate_mutual_inductive(&block, &env, &config)
        .expect("single inductive should elaborate");

    assert_eq!(result.decl.types.len(), 1);
    assert_eq!(result.inductive_vals.len(), 1);
    assert_eq!(result.constructor_vals.len(), 2);
    assert_eq!(result.recursor_specs.len(), 1);
    assert!(result.large_elim);

    // Check InductiveVal properties.
    let ind_val = &result.inductive_vals[0];
    assert_eq!(ind_val.name, nat);
    assert!(ind_val.is_recursive);
    assert_eq!(ind_val.constructor_names.len(), 2);

    // Check ConstructorVal properties.
    assert_eq!(
        result.constructor_vals[0].name,
        Name::from_string("Nat.zero")
    );
    assert_eq!(result.constructor_vals[0].num_fields, 0);
    assert_eq!(
        result.constructor_vals[1].name,
        Name::from_string("Nat.succ")
    );
    assert_eq!(result.constructor_vals[1].num_fields, 1);
}

#[test]
fn test_elaborate_mutual_tree_forest() {
    let env = Environment::new();
    let tree = Name::from_string("Tree");
    let forest = Name::from_string("Forest");
    let tree_const = Expr::const_(tree.clone(), vec![]);
    let forest_const = Expr::const_(forest.clone(), vec![]);

    let block = MutualInductiveBlock {
        types: vec![
            InductiveTypeInfo {
                name: tree.clone(),
                type_expr: type_0(),
                constructors: vec![ctor(
                    "Tree.node",
                    arrow(forest_const.clone(), tree_const.clone()),
                )],
                is_recursive: true,
                references_siblings: true,
            },
            InductiveTypeInfo {
                name: forest.clone(),
                type_expr: type_0(),
                constructors: vec![
                    ctor("Forest.nil", forest_const.clone()),
                    ctor(
                        "Forest.cons",
                        arrow(tree_const, arrow(forest_const.clone(), forest_const)),
                    ),
                ],
                is_recursive: true,
                references_siblings: true,
            },
        ],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    let config = MutualIndConfig::default();
    let result = elaborate_mutual_inductive(&block, &env, &config)
        .expect("mutual tree/forest should elaborate");

    assert_eq!(result.decl.types.len(), 2);
    assert_eq!(result.inductive_vals.len(), 2);
    assert_eq!(result.constructor_vals.len(), 3);
    assert_eq!(result.recursor_specs.len(), 2);

    // Check that all_names is correct for both.
    for ind_val in &result.inductive_vals {
        assert_eq!(ind_val.all_names.len(), 2);
    }
}

#[test]
fn test_elaborate_positivity_violation_rejected() {
    let env = Environment::new();
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");

    let block = MutualInductiveBlock {
        types: vec![InductiveTypeInfo {
            name: bad.clone(),
            type_expr: type_0(),
            constructors: vec![ctor(
                "Bad.mk",
                // (Bad -> Bool) -> Bad : non-positive
                arrow(arrow(bad_const.clone(), bool_const), bad_const),
            )],
            is_recursive: false,
            references_siblings: false,
        }],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    let config = MutualIndConfig::default();
    let result = elaborate_mutual_inductive(&block, &env, &config);
    assert!(result.is_err(), "non-positive should be rejected");
}

#[test]
fn test_elaborate_positivity_disabled() {
    let env = Environment::new();
    let bad = Name::from_string("Bad");
    let bad_const = Expr::const_(bad.clone(), vec![]);
    let bool_const = Expr::const_str("Bool");

    let block = MutualInductiveBlock {
        types: vec![InductiveTypeInfo {
            name: bad.clone(),
            type_expr: type_0(),
            constructors: vec![ctor(
                "Bad.mk",
                arrow(arrow(bad_const.clone(), bool_const), bad_const),
            )],
            is_recursive: false,
            references_siblings: false,
        }],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    let config = MutualIndConfig {
        check_positivity: false,
        ..Default::default()
    };
    // With positivity check disabled, this should succeed.
    elaborate_mutual_inductive(&block, &env, &config)
        .expect("should pass with positivity disabled");
}

#[test]
fn test_elaborate_no_recursors() {
    let env = Environment::new();
    let block = make_block(vec![simple_type("Unit")]);
    let config = MutualIndConfig {
        generate_recursors: false,
        ..Default::default()
    };
    let result = elaborate_mutual_inductive(&block, &env, &config)
        .expect("should elaborate without recursors");
    assert!(result.recursor_specs.is_empty());
}

#[test]
fn test_elaborate_empty_constructor_type() {
    // Like False : Prop with no constructors.
    let env = Environment::new();
    let block = MutualInductiveBlock {
        types: vec![InductiveTypeInfo {
            name: Name::from_string("False"),
            type_expr: prop(),
            constructors: Vec::new(),
            is_recursive: false,
            references_siblings: false,
        }],
        universe_params: Vec::new(),
        num_params: 0,
        is_unsafe: false,
    };
    let config = MutualIndConfig::default();
    let result = elaborate_mutual_inductive(&block, &env, &config)
        .expect("False-like type should elaborate");
    assert_eq!(result.constructor_vals.len(), 0);
    assert_eq!(result.recursor_specs.len(), 1); // rec still generated
    assert_eq!(result.recursor_specs[0].val.num_minors, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge case tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_config_default_values() {
    let config = MutualIndConfig::default();
    assert!(config.check_positivity);
    assert!(config.generate_recursors);
    assert_eq!(config.max_mutual_types, 32);
}

#[test]
fn test_positivity_result_equality() {
    let r1 = PositivityResult::StrictlyPositive;
    let r2 = PositivityResult::StrictlyPositive;
    assert_eq!(r1, r2);

    let r3 = PositivityResult::NonPositive {
        offender: Name::from_string("X"),
        location: "test".to_string(),
    };
    let r4 = PositivityResult::NonPositive {
        offender: Name::from_string("X"),
        location: "test".to_string(),
    };
    assert_eq!(r3, r4);
    assert_ne!(r1, r3);
}

#[test]
fn test_extract_sort_level_non_sort() {
    // If the type expression is not a Sort, extract_sort_level returns zero.
    let expr = Expr::const_str("Nat");
    let level = extract_sort_level(&expr);
    assert_eq!(level, Level::zero());
}

#[test]
fn test_three_way_mutual() {
    let env = Environment::new();
    let a = Name::from_string("A");
    let b = Name::from_string("B");
    let c = Name::from_string("C");
    let a_const = Expr::const_(a.clone(), vec![]);
    let b_const = Expr::const_(b.clone(), vec![]);
    let c_const = Expr::const_(c.clone(), vec![]);

    let block = MutualInductiveBlock {
        types: vec![
            InductiveTypeInfo {
                name: a.clone(),
                type_expr: type_0(),
                constructors: vec![ctor("A.mk", arrow(b_const.clone(), a_const.clone()))],
                is_recursive: true,
                references_siblings: true,
            },
            InductiveTypeInfo {
                name: b.clone(),
                type_expr: type_0(),
                constructors: vec![ctor("B.mk", arrow(c_const.clone(), b_const.clone()))],
                is_recursive: true,
                references_siblings: true,
            },
            InductiveTypeInfo {
                name: c.clone(),
                type_expr: type_0(),
                constructors: vec![ctor("C.mk", arrow(a_const, c_const))],
                is_recursive: true,
                references_siblings: true,
            },
        ],
        universe_params: vec![Name::from_string("u")],
        num_params: 0,
        is_unsafe: false,
    };

    let config = MutualIndConfig::default();
    let result = elaborate_mutual_inductive(&block, &env, &config)
        .expect("three-way mutual should elaborate");

    assert_eq!(result.decl.types.len(), 3);
    assert_eq!(result.recursor_specs.len(), 3);

    for spec in &result.recursor_specs {
        assert_eq!(spec.val.num_motives, 3);
        assert_eq!(spec.val.num_minors, 3); // one ctor per type
    }
}
