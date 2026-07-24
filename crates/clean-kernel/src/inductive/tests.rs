// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::expr::BinderInfo;
use crate::level::Level;
use crate::Environment;
use std::sync::Arc;

/// Helper: single-name positivity check for tests with only one inductive.
fn check_pos(name: &Name, expr: &Expr, param_count: u32) -> Result<(), InductiveError> {
    check_positivity(name, expr, param_count, &[name])
}

#[test]
fn test_positivity_simple() {
    // Nat : Type
    // zero : Nat (positive - Nat only in return type)
    let nat = Name::from_string("Nat");
    let zero_type = Expr::const_(nat.clone(), vec![]);
    check_pos(&nat, &zero_type, 0).expect("Nat in return type only should be positive");
}

#[test]
fn test_positivity_arrow() {
    // succ : Nat → Nat (positive - Nat in domain is OK for non-dependent arrow)
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let succ_type = Expr::arrow(nat_ref.clone(), nat_ref.clone());
    check_pos(&nat, &succ_type, 0).expect("Nat → Nat should be positive");
}

#[test]
fn test_positivity_negative() {
    // Bad : (Bad → Nat) → Bad (negative - Bad appears left of arrow)
    let bad = Name::from_string("Bad");
    let nat = Name::from_string("Nat");
    let bad_ref = Expr::const_(bad.clone(), vec![]);
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    // (Bad → Nat) → Bad
    let inner_arrow = Expr::arrow(bad_ref.clone(), nat_ref);
    let bad_type = Expr::arrow(inner_arrow, bad_ref);

    let err = check_pos(&bad, &bad_type, 0).unwrap_err();
    assert!(
        matches!(err, InductiveError::NonPositive(..)),
        "(Bad → Nat) → Bad should fail with NonPositive, got: {err}"
    );
}

#[test]
fn test_positivity_nested_positive() {
    // Tree : Type
    // node : List Tree → Tree
    // This is positive because Tree appears as argument to List, not directly in arrow domain

    let tree = Name::from_string("Tree");
    let list = Name::from_string("List");
    let tree_ref = Expr::const_(tree.clone(), vec![]);
    let list_tree = Expr::app(Expr::const_(list, vec![]), tree_ref.clone());
    let node_type = Expr::arrow(list_tree, tree_ref);

    // This should be positive (Tree is applied to List, then List Tree → Tree)
    check_pos(&tree, &node_type, 0).expect("Nested positive (List Tree → Tree) should be accepted");
}

/// Mutual A/B where B occurs negatively in A.mk: (B → Nat) → A (#2135).
#[test]
fn test_positivity_mutual_inductive_cross_type_negative() {
    let (a, b) = (Name::from_string("A"), Name::from_string("B"));
    let (a_ref, b_ref) = (
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    // A.mk : (B → Nat) → A — B left of arrow = non-positive
    let a_mk = Expr::arrow(Expr::arrow(b_ref.clone(), nat_ref), a_ref.clone());
    // B.mk : A → B — positive
    let b_mk = Expr::arrow(a_ref, b_ref);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    let result = validate_inductive(&decl);
    // Verify B is the name detected in a non-positive position
    assert!(
        matches!(result, Err(InductiveError::NonPositive(ref name, _)) if *name == b),
        "Should detect B in non-positive position in A.mk, got {result:?}"
    );
}

/// Valid Even/Odd mutual inductive — all occurrences strictly positive (#2135).
#[test]
fn test_positivity_mutual_inductive_even_odd_valid() {
    let (even, odd) = (Name::from_string("Even"), Name::from_string("Odd"));
    let (e_ref, o_ref) = (
        Expr::const_(even.clone(), vec![]),
        Expr::const_(odd.clone(), vec![]),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: even.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Even.zero"),
                        type_: e_ref.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Even.succ_odd"),
                        type_: Expr::arrow(o_ref.clone(), e_ref.clone()),
                    },
                ],
            },
            InductiveType {
                name: odd.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("Odd.succ_even"),
                    type_: Expr::arrow(e_ref, o_ref),
                }],
            },
        ],
    };
    validate_inductive(&decl).expect("Valid Even/Odd mutual inductive should pass");
}

/// Indexed mutual inductive where sibling type B appears as an index
/// argument to A: A.mk : A (B Unit) → A Unit (#2145).
///
/// Lean 4's is_valid_ind_app checks index args against ALL mutual types
/// via has_ind_occ. Without this, clean would accept the definition because
/// check_no_negative_occurrence only checked args against the single
/// inductive_name being validated.
#[test]
fn test_positivity_mutual_index_arg_cross_type_rejected() {
    let (a, b) = (Name::from_string("A"), Name::from_string("B"));
    let unit = Name::from_string("Unit");
    let (a_ref, b_ref) = (
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    let unit_ref = Expr::const_(unit.clone(), vec![]);

    // B Unit — B applied to Unit
    let b_unit = Expr::app(b_ref.clone(), unit_ref.clone());
    // A (B Unit) — A applied to index (B Unit), contains mutual type B
    let a_b_unit = Expr::app(a_ref.clone(), b_unit);
    // A Unit — A applied to index Unit
    let a_unit = Expr::app(a_ref.clone(), unit_ref.clone());

    // A.mk : A (B Unit) → A Unit
    let a_mk = Expr::arrow(a_b_unit, a_unit);
    // B.mk : Unit → B Unit (standard positive constructor)
    let b_mk = Expr::arrow(
        unit_ref,
        Expr::app(
            b_ref.clone(),
            Expr::const_(Name::from_string("Unit"), vec![]),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    let result = validate_inductive(&decl);
    assert!(
        result.is_err(),
        "Mutual type B in index arg of A should be rejected (#2145), got {result:?}"
    );
    assert!(
        matches!(result, Err(InductiveError::NonPositive(ref name, _)) if *name == b),
        "Should detect B in index position of A, got {result:?}"
    );
}

/// Valid mutual inductive where sibling appears in direct (non-index) position.
/// Even.succ_odd : Odd → Even is fine because Odd appears directly as an arg,
/// not as an index to Even-headed application.
#[test]
fn test_positivity_mutual_direct_arg_accepted() {
    // This is the Even/Odd case already tested, but here we verify it
    // with the new all_ind_names plumbing via check_pos directly.
    let (a, b) = (Name::from_string("A"), Name::from_string("B"));
    let (a_ref, b_ref) = (
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    // A.mk : B → A — B is a direct argument, not an index to an A-headed app
    let a_mk = Expr::arrow(b_ref.clone(), a_ref.clone());
    // B.mk : B (nullary)
    let b_mk = b_ref.clone();
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    validate_inductive(&decl).expect("B as direct arg (not index) of A should pass positivity");
}

#[test]
fn test_mentions_name() {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    assert!(mentions_name(&nat_ref, &nat));
    assert!(!mentions_name(&Expr::prop(), &nat));

    let arrow = Expr::arrow(nat_ref.clone(), Expr::prop());
    assert!(mentions_name(&arrow, &nat));
}

#[test]
fn test_count_pi_args() {
    // Nat → Nat → Nat has 2 Pi's
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let ty = Expr::arrow(nat_ref.clone(), Expr::arrow(nat_ref.clone(), nat_ref));
    assert_eq!(count_pi_args(&ty), 2);

    // Nat has 0 Pi's
    assert_eq!(
        count_pi_args(&Expr::const_(Name::from_string("Nat"), vec![])),
        0
    );
}

#[test]
fn test_strip_pi_exact_partial_and_overshoot() {
    // Pins strip_pi behavior across the for-loop rewrite (Trust ledger
    // 2026-06-10: panic_boundary Overflow(Sub) @ inductive/mod.rs:627).
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    // Prop → Prop → Nat
    let ty = Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), nat_ref.clone()));

    // n = 0: unchanged
    assert_eq!(strip_pi(&ty, 0), &ty);

    // n = 1: strips one Pi
    assert!(matches!(strip_pi(&ty, 1).kind, ExprKind::Pi(_, _, _)));

    // n = 2 (exact): reaches the codomain
    assert!(matches!(
        &strip_pi(&ty, 2).kind,
        ExprKind::Const(n, _) if n == &Name::from_string("Nat")
    ));

    // n > pi count (incl. u32::MAX): break path, returns codomain, no panic
    assert_eq!(strip_pi(&ty, 3), strip_pi(&ty, 2));
    assert_eq!(strip_pi(&ty, u32::MAX), strip_pi(&ty, 2));

    // non-Pi expression: returned unchanged for any n
    assert_eq!(strip_pi(&nat_ref, u32::MAX), &nat_ref);
}

#[test]
fn test_get_return_type() {
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let ty = Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), nat_ref.clone()));

    let ret = get_return_type(&ty);
    assert!(matches!(
        &ret.kind,
        ExprKind::Const(n, _) if n == &Name::from_string("Nat")
    ));
}

#[test]
fn test_is_recursive() {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let zero = Constructor {
        name: Name::from_string("Nat.zero"),
        type_: nat_ref.clone(),
    };
    let succ = Constructor {
        name: Name::from_string("Nat.succ"),
        type_: Expr::arrow(nat_ref.clone(), nat_ref),
    };

    // Just zero is not recursive
    assert!(!is_recursive(
        std::slice::from_ref(&nat),
        std::slice::from_ref(&zero)
    ));

    // With succ it is recursive
    assert!(is_recursive(&[nat], &[zero, succ]));
}

#[test]
fn test_is_reflexive_nat() {
    // Nat is recursive but NOT reflexive
    // succ : Nat → Nat - Nat appears directly as an argument, not in a function domain
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let zero = Constructor {
        name: Name::from_string("Nat.zero"),
        type_: nat_ref.clone(),
    };
    let succ = Constructor {
        name: Name::from_string("Nat.succ"),
        type_: Expr::arrow(nat_ref.clone(), nat_ref),
    };

    assert!(!is_reflexive(
        std::slice::from_ref(&nat),
        std::slice::from_ref(&zero)
    ));
    assert!(!is_reflexive(&[nat], &[zero, succ]));
}

#[test]
fn test_is_reflexive_w_type() {
    // W-type (well-founded trees) IS reflexive
    // sup : (a : A) → (B a → W A B) → W A B
    // W appears in the domain of (B a → W A B)
    let w = Name::from_string("W");
    let a = Name::from_string("A");
    let b = Name::from_string("B");

    let w_ref = Expr::const_(w.clone(), vec![]);
    let a_ref = Expr::const_(a.clone(), vec![]);
    let b_ref = Expr::const_(b.clone(), vec![]);

    // B a → W A B (the function type with W in domain position is the argument)
    let b_a = Expr::app(b_ref.clone(), a_ref.clone());
    let inner_arrow = Expr::arrow(b_a, w_ref.clone());

    // (a : A) → (B a → W A B) → W A B
    let sup_type = Expr::pi(
        BinderInfo::Default,
        a_ref.clone(),
        Expr::arrow(inner_arrow, w_ref),
    );

    let sup = Constructor {
        name: Name::from_string("W.sup"),
        type_: sup_type,
    };

    assert!(is_reflexive(&[w], &[sup]));
}

#[test]
fn test_is_reflexive_list() {
    // List is recursive but NOT reflexive
    // cons : A → List A → List A
    // List appears directly as an argument, not in a function domain
    let list = Name::from_string("List");
    let a = Name::from_string("A");

    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![]),
        Expr::const_(a.clone(), vec![]),
    );

    let nil = Constructor {
        name: Name::from_string("List.nil"),
        type_: list_a.clone(),
    };
    let cons = Constructor {
        name: Name::from_string("List.cons"),
        // A → List A → List A
        type_: Expr::arrow(Expr::const_(a, vec![]), Expr::arrow(list_a.clone(), list_a)),
    };

    assert!(!is_reflexive(&[list], &[nil, cons]));
}

#[test]
fn test_is_reflexive_nested_function() {
    // Test with nested function types
    // T : Type
    // mk : ((T → T) → T) → T
    // T appears in domain of (T → T), which is in domain of outer arrow
    // This IS reflexive
    let t = Name::from_string("T");
    let t_ref = Expr::const_(t.clone(), vec![]);

    // T → T
    let t_to_t = Expr::arrow(t_ref.clone(), t_ref.clone());
    // (T → T) → T
    let inner = Expr::arrow(t_to_t, t_ref.clone());
    // ((T → T) → T) → T
    let mk_type = Expr::arrow(inner, t_ref);

    let mk = Constructor {
        name: Name::from_string("T.mk"),
        type_: mk_type,
    };

    assert!(is_reflexive(&[t], &[mk]));
}

#[test]
fn test_is_recursive_mutual_even_odd() {
    // Mutual inductive Even/Odd:
    //   inductive Even : Nat → Prop
    //   | zero : Even 0
    //   | succ_odd : Odd n → Even (n+1)
    //
    //   inductive Odd : Nat → Prop
    //   | succ_even : Even n → Odd (n+1)
    //
    // Even's constructor mentions Odd, not Even itself.
    // With only Even's name, is_recursive should be false (the old bug).
    // With the full mutual block [Even, Odd], is_recursive should be true.
    let even = Name::from_string("Even");
    let odd = Name::from_string("Odd");
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // Even.zero : Nat → Even 0  (simplified: just returns Even-applied)
    let even_ref = Expr::const_(even.clone(), vec![]);
    let odd_ref = Expr::const_(odd.clone(), vec![]);

    let even_zero = Constructor {
        name: Name::from_string("Even.zero"),
        type_: Expr::app(even_ref.clone(), nat_ref.clone()),
    };
    // Even.succ_odd : Odd n → Even (n+1)
    // The key: constructor of Even mentions Odd in its argument
    let even_succ_odd = Constructor {
        name: Name::from_string("Even.succ_odd"),
        type_: Expr::arrow(
            Expr::app(odd_ref.clone(), nat_ref.clone()),
            Expr::app(even_ref.clone(), nat_ref.clone()),
        ),
    };

    // Bug case: checking only Even's own name misses the cross-reference to Odd
    assert!(
        !is_recursive(
            std::slice::from_ref(&even),
            &[even_zero.clone(), even_succ_odd.clone()]
        ),
        "Even's constructors don't mention Even itself"
    );

    // Fixed: checking the full mutual block [Even, Odd] detects the cross-reference
    assert!(
        is_recursive(&[even.clone(), odd.clone()], &[even_zero, even_succ_odd]),
        "Even's constructors mention Odd, which is in the mutual block"
    );

    // Odd.succ_even : Even n → Odd (n+1)
    let odd_succ_even = Constructor {
        name: Name::from_string("Odd.succ_even"),
        type_: Expr::arrow(
            Expr::app(even_ref, nat_ref.clone()),
            Expr::app(odd_ref, nat_ref),
        ),
    };

    // Odd's constructor mentions Even — same pattern
    assert!(
        !is_recursive(
            std::slice::from_ref(&odd),
            std::slice::from_ref(&odd_succ_even)
        ),
        "Odd's constructors don't mention Odd itself"
    );
    assert!(
        is_recursive(&[even, odd], &[odd_succ_even]),
        "Odd's constructors mention Even, which is in the mutual block"
    );
}

#[test]
fn test_is_reflexive_mutual_cross_reference() {
    // Mutual inductive where one type appears in a function domain of the other's constructor.
    //   inductive A : Type
    //   | mk : (B → A) → A
    //
    //   inductive B : Type
    //   | mk : A → B
    //
    // A.mk has argument type (B → A) — B appears in the domain of a function type.
    // With only A's name, is_reflexive is false (A appears in codomain, not domain).
    // With [A, B], is_reflexive should be true because B appears in the domain.
    let a = Name::from_string("A");
    let b = Name::from_string("B");
    let a_ref = Expr::const_(a.clone(), vec![]);
    let b_ref = Expr::const_(b.clone(), vec![]);

    // A.mk : (B → A) → A
    let a_mk = Constructor {
        name: Name::from_string("A.mk"),
        type_: Expr::arrow(Expr::arrow(b_ref.clone(), a_ref.clone()), a_ref.clone()),
    };

    // With only A's name: A appears in codomain of (B → A), which is a Pi domain.
    // But domain of the inner Pi is B, codomain is A.
    // is_function_mentioning_name checks both domain and codomain of the Pi.
    // So with just [A], it IS reflexive (A appears in the function type).
    assert!(
        is_reflexive(std::slice::from_ref(&a), std::slice::from_ref(&a_mk)),
        "A appears in the function-typed arg (B → A)"
    );

    // With the full mutual block [A, B], also reflexive (B appears in domain too)
    assert!(
        is_reflexive(&[a.clone(), b.clone()], &[a_mk]),
        "Both A and B appear in the function-typed arg (B → A)"
    );

    // B.mk : A → B (not reflexive — A is a direct argument, not in a function domain)
    let b_mk = Constructor {
        name: Name::from_string("B.mk"),
        type_: Expr::arrow(a_ref, b_ref),
    };

    assert!(
        !is_reflexive(std::slice::from_ref(&b), std::slice::from_ref(&b_mk)),
        "B.mk has direct arg A, not in a function domain"
    );
    // Even with the full mutual block, it's not reflexive —
    // A is a direct argument, not inside a Pi domain
    assert!(
        !is_reflexive(&[a, b], &[b_mk]),
        "B.mk's arg A is direct, not in a function domain"
    );
}

#[test]
fn test_validate_inductive_nat() {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };

    validate_inductive(&decl).expect("Nat with zero and succ should validate");
}

#[test]
fn test_validate_inductive_negative() {
    // Try to define a type that violates positivity
    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                // (Bad → Bad) → Bad is negative
                type_: Expr::arrow(Expr::arrow(bad_ref.clone(), bad_ref.clone()), bad_ref),
            }],
        }],
    };

    let err = validate_inductive(&decl).unwrap_err();
    assert!(
        matches!(err, InductiveError::NonPositive(..)),
        "Negative inductive should fail with NonPositive, got: {err}"
    );
}

#[test]
fn test_allows_large_elim() {
    let env = Environment::new();

    // Type in Type allows large elim
    let nat_type = Expr::type_();
    assert!(allows_large_elim(&env, &nat_type, &[], 0, 1));

    // Type in Prop with no constructors allows large elim (Empty/False)
    let empty_type = Expr::prop();
    assert!(allows_large_elim(&env, &empty_type, &[], 0, 1));

    // Type in Prop with one constructor, no non-param fields → large elim
    // Unit.unit : Unit (constructor returns the inductive directly, 0 params)
    let unit_ctor = Constructor {
        name: Name::from_string("Unit.unit"),
        type_: Expr::const_(Name::from_string("Unit"), vec![]),
    };
    assert!(allows_large_elim(&env, &empty_type, &[unit_ctor], 0, 1));

    // Nonempty-like: Prop inductive with 1 param and 1 non-Prop field
    // Nonempty (α : Sort u) : Prop
    // Nonempty.intro (α : Sort u) → (val : α) → Nonempty α
    // The field `val : α` is Sort u (not Prop), and doesn't appear in indices
    // → should NOT allow large elimination
    let u = Level::param(Name::from_string("u"));
    let nonempty_type = Expr::pi(BinderInfo::Default, Expr::sort(u.clone()), Expr::prop());
    let nonempty_ctor = Constructor {
        name: Name::from_string("Nonempty.intro"),
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::sort(u.clone()), // param α : Sort u
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0), // val : α
                Expr::app(
                    Expr::const_(Name::from_string("Nonempty"), vec![u.clone()]),
                    Expr::bvar(1), // Nonempty α
                ),
            ),
        ),
    };
    assert!(
        !allows_large_elim(&env, &nonempty_type, &[nonempty_ctor], 1, 1),
        "Nonempty-like Prop inductive with non-Prop field should NOT allow large elimination"
    );
}

// =========================================================================
// Mutation Testing Kill Tests - inductive.rs survivors
// =========================================================================

#[test]
fn test_mentions_name_logic_operators() {
    // Kill mutants: replace || with && in mentions_name (lines 293)
    // mentions_name returns true if ANY subexpression contains the name

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let other = Expr::const_(Name::from_string("Other"), vec![]);

    // App: should find name in either f OR a
    let app_in_f = Expr::app(nat_ref.clone(), other.clone());
    let app_in_a = Expr::app(other.clone(), nat_ref.clone());
    let app_neither = Expr::app(other.clone(), other.clone());

    assert!(
        mentions_name(&app_in_f, &nat),
        "Should find Nat in function position"
    );
    assert!(
        mentions_name(&app_in_a, &nat),
        "Should find Nat in argument position"
    );
    assert!(
        !mentions_name(&app_neither, &nat),
        "Should not find Nat when absent"
    );

    // Let: should find name in ANY of ty, val, or body
    let let_in_ty = Expr::let_named(
        Name::anon(),
        nat_ref.clone(),
        other.clone(),
        other.clone(),
        false,
    );
    let let_in_val = Expr::let_named(
        Name::anon(),
        other.clone(),
        nat_ref.clone(),
        other.clone(),
        false,
    );
    let let_in_body = Expr::let_named(
        Name::anon(),
        other.clone(),
        other.clone(),
        nat_ref.clone(),
        false,
    );
    let let_none = Expr::let_named(
        Name::anon(),
        other.clone(),
        other.clone(),
        other.clone(),
        false,
    );

    assert!(
        mentions_name(&let_in_ty, &nat),
        "Should find Nat in let type"
    );
    assert!(
        mentions_name(&let_in_val, &nat),
        "Should find Nat in let value"
    );
    assert!(
        mentions_name(&let_in_body, &nat),
        "Should find Nat in let body"
    );
    assert!(
        !mentions_name(&let_none, &nat),
        "Should not find Nat when absent from let"
    );
}

#[test]
fn test_strip_pi_comparison_and_arithmetic() {
    // Kill mutants:
    // - replace == with != in strip_pi (line 309)
    // - delete match arm Expr::from_kind(ExprKind::Pi) in strip_pi (line 313)
    // - replace - with / or + in strip_pi (line 313)

    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // n=0 should return the expression unchanged
    let simple = nat_ref.clone();
    assert!(
        std::ptr::eq(strip_pi(&simple, 0), &simple),
        "strip_pi(e, 0) should return e"
    );

    // Single Pi - strip 1 should return body
    let single_pi = Expr::pi(BinderInfo::Default, Expr::prop(), nat_ref.clone());
    let stripped1 = strip_pi(&single_pi, 1);
    assert!(matches!(
        &stripped1.kind,
        ExprKind::Const(n, _) if n == &Name::from_string("Nat")
    ));

    // Strip 0 from Pi should return the Pi itself
    let stripped0 = strip_pi(&single_pi, 0);
    assert!(matches!(&stripped0.kind, ExprKind::Pi(_, _, _)));

    // Two Pis - strip 1 should return inner Pi, strip 2 should return body
    let inner_pi = Expr::pi(BinderInfo::Default, Expr::type_(), nat_ref.clone());
    let double_pi = Expr::pi(BinderInfo::Default, Expr::prop(), inner_pi);

    let stripped_1of2 = strip_pi(&double_pi, 1);
    assert!(
        matches!(&stripped_1of2.kind, ExprKind::Pi(_, _, _)),
        "Stripping 1 from 2 Pis should leave 1 Pi"
    );

    let stripped_2of2 = strip_pi(&double_pi, 2);
    assert!(matches!(
        &stripped_2of2.kind,
        ExprKind::Const(n, _) if n == &Name::from_string("Nat")
    ));

    // Try to strip more than available - should return the final body
    let stripped_3of2 = strip_pi(&double_pi, 3);
    assert!(matches!(
        &stripped_3of2.kind,
        ExprKind::Const(n, _) if n == &Name::from_string("Nat")
    ));
}

#[test]
fn test_strip_pi_arithmetic_precise() {
    // Kill mutants: n - 1 replaced with n / 1, n + 1, etc.
    // We need tests that distinguish between n-1 and n/1, n+1

    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // Build a chain of 5 Pi types
    let mut expr = nat_ref.clone();
    for i in 0..5 {
        expr = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string(&format!("Arg{i}")), vec![]),
            expr,
        );
    }

    // strip_pi(e, 1) should strip exactly 1 (body is Pi with 4 remaining)
    // n-1: after stripping 1, count_pi_args should be 4
    // n/1: would strip 1, still 4
    // n+1: would try to strip 2, leaving 3
    let after_1 = strip_pi(&expr, 1);
    assert_eq!(count_pi_args(after_1), 4, "Stripping 1 should leave 4 Pis");

    // strip_pi(e, 2) should strip exactly 2
    let after_2 = strip_pi(&expr, 2);
    assert_eq!(count_pi_args(after_2), 3, "Stripping 2 should leave 3 Pis");

    // strip_pi(e, 3) should strip exactly 3
    let after_3 = strip_pi(&expr, 3);
    assert_eq!(count_pi_args(after_3), 2, "Stripping 3 should leave 2 Pis");

    // This test specifically catches n-1 vs n+1: with 5 Pis, stripping 2:
    // Correct (n-1): strips 2, leaves 3
    // Wrong (n+1): would try to strip 3, leaves 2
    assert_ne!(
        count_pi_args(after_2),
        2,
        "n-1 vs n+1 distinction: should not be 2"
    );
}

#[test]
fn test_validate_inductive_match_guard() {
    // Kill mutant: replace match guard name == &ind_type.name with true (line 428)
    // This should verify constructor returns the correct inductive type

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let other = Name::from_string("Other");
    let other_ref = Expr::const_(other.clone(), vec![]);

    // Valid: constructor returns the inductive type
    let valid_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.zero"),
                type_: nat_ref.clone(), // Returns Nat
            }],
        }],
    };
    validate_inductive(&valid_decl).expect("Nat with only zero should validate");

    // Invalid: constructor returns a DIFFERENT type
    let invalid_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.bad"),
                type_: other_ref.clone(), // Returns Other, not Nat!
            }],
        }],
    };
    assert!(
        validate_inductive(&invalid_decl).is_err(),
        "Constructor returning wrong type should fail validation"
    );

    // Invalid: constructor returns wrong type after arrow
    let invalid_arrow = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.bad2"),
                type_: Expr::arrow(nat_ref.clone(), other_ref.clone()), // Nat → Other
            }],
        }],
    };
    assert!(
        validate_inductive(&invalid_arrow).is_err(),
        "Constructor with wrong return type should fail"
    );
}

#[test]
fn test_allows_large_elim_prop_multiple_constructors() {
    // Kill mutant: replace allows_large_elim with true (line 470)
    // Prop types with multiple constructors should NOT allow large elimination

    let env = Environment::new();
    let prop_type = Expr::prop();

    // In Prop with 2 constructors - should NOT allow large elim
    let ctor1 = Constructor {
        name: Name::from_string("Or.inl"),
        type_: Expr::const_(Name::from_string("Or"), vec![]),
    };
    let ctor2 = Constructor {
        name: Name::from_string("Or.inr"),
        type_: Expr::const_(Name::from_string("Or"), vec![]),
    };

    assert!(
        !allows_large_elim(&env, &prop_type, &[ctor1.clone(), ctor2.clone()], 0, 1),
        "Prop type with 2 constructors should NOT allow large elimination"
    );

    // In Prop with 3 constructors
    let ctor3 = Constructor {
        name: Name::from_string("Or.third"),
        type_: Expr::const_(Name::from_string("Or"), vec![]),
    };
    let ctors = vec![
        Constructor {
            name: Name::from_string("C1"),
            type_: Expr::const_(Name::from_string("T"), vec![]),
        },
        Constructor {
            name: Name::from_string("C2"),
            type_: Expr::const_(Name::from_string("T"), vec![]),
        },
        ctor3,
    ];

    assert!(
        !allows_large_elim(&env, &prop_type, &ctors, 0, 1),
        "Prop type with 3 constructors should NOT allow large elimination"
    );

    // But Type (not Prop) with multiple constructors DOES allow large elim
    let type_type = Expr::type_();
    assert!(
        allows_large_elim(&env, &type_type, &[ctor1, ctor2], 0, 1),
        "Type (not Prop) should allow large elimination"
    );
}

#[test]
fn test_allows_large_elim_mutual_prop_only() {
    // Lean 4 inductive.cpp:486-489: mutual predicates (Prop-valued) are restricted
    // to Prop-only elimination. Even with a single constructor per type, if the
    // mutual block has >1 type and all are in Prop, large elimination is forbidden.

    let env = Environment::new();
    let prop_type = Expr::prop();

    // Single Prop type with one constructor DOES allow large elim (e.g., Eq)
    let ctor = Constructor {
        name: Name::from_string("Single.mk"),
        type_: Expr::const_(Name::from_string("Single"), vec![]),
    };
    assert!(
        allows_large_elim(&env, &prop_type, std::slice::from_ref(&ctor), 0, 1),
        "Single Prop inductive with 1 ctor should allow large elimination"
    );

    // Same Prop type with one constructor but in a mutual block of 2 types
    // should NOT allow large elimination
    assert!(
        !allows_large_elim(&env, &prop_type, std::slice::from_ref(&ctor), 0, 2),
        "Mutual Prop inductive (2 types) should NOT allow large elimination"
    );

    // Mutual block of 3 types, same check
    assert!(
        !allows_large_elim(&env, &prop_type, &[ctor], 0, 3),
        "Mutual Prop inductive (3 types) should NOT allow large elimination"
    );

    // Mutual block in Type (not Prop) should still allow large elim
    let type_type = Expr::type_();
    let type_ctor = Constructor {
        name: Name::from_string("TypeMutual.mk"),
        type_: Expr::const_(Name::from_string("TypeMutual"), vec![]),
    };
    assert!(
        allows_large_elim(&env, &type_type, &[type_ctor], 0, 2),
        "Mutual Type inductive should still allow large elimination"
    );
}

// =========================================================================
// InductiveError error path tests
// These tests verify the validation rejects malformed inductive declarations
// with the appropriate error type.
// =========================================================================

/// Test that empty inductive declaration triggers EmptyDecl error
#[test]
fn test_error_empty_decl() {
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![], // Empty!
    };

    let result = validate_inductive(&decl);
    assert!(
        matches!(result, Err(InductiveError::EmptyDecl)),
        "Expected EmptyDecl, got {result:?}"
    );
}

/// Test that non-positive occurrence triggers NonPositive error
#[test]
fn test_error_non_positive() {
    // Bad : Type where mk : (Bad → Bad) → Bad
    // Bad appears on the left of an arrow within the domain
    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                // (Bad → Bad) → Bad is negative occurrence
                type_: Expr::arrow(Expr::arrow(bad_ref.clone(), bad_ref.clone()), bad_ref),
            }],
        }],
    };

    let result = validate_inductive(&decl);
    assert!(
        matches!(result, Err(InductiveError::NonPositive(ref name, ref culprit))
            if *name == bad && *culprit == bad),
        "Expected NonPositive for Bad, got {result:?}"
    );
}

/// Test that constructor not returning inductive type triggers ConstructorReturnType error
#[test]
fn test_error_constructor_return_type() {
    let my_type = Name::from_string("MyType");
    let nat = Name::from_string("Nat");

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: my_type.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("MyType.wrong"),
                // Constructor returns Nat instead of MyType
                type_: Expr::const_(nat.clone(), vec![]),
            }],
        }],
    };

    let result = validate_inductive(&decl);
    assert!(
        matches!(result, Err(InductiveError::ConstructorReturnType(ref ctor_name, ref ind_name))
            if *ctor_name == Name::from_string("MyType.wrong")
            && *ind_name == Name::from_string("MyType")),
        "Expected ConstructorReturnType, got {result:?}"
    );
}

/// Test that constructor returning wrong inductive in mutual block triggers error
#[test]
fn test_error_constructor_return_wrong_type_in_mutual() {
    // Even/Odd mutual inductive where Even.succ returns Odd but declared in Even
    let even = Name::from_string("Even");
    let odd = Name::from_string("Odd");

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: even.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Even.zero"),
                        type_: Expr::const_(even.clone(), vec![]),
                    },
                    Constructor {
                        name: Name::from_string("Even.bad"),
                        // Returns Odd instead of Even
                        type_: Expr::const_(odd.clone(), vec![]),
                    },
                ],
            },
            InductiveType {
                name: odd.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("Odd.zero"),
                    type_: Expr::const_(odd.clone(), vec![]),
                }],
            },
        ],
    };

    let result = validate_inductive(&decl);
    assert!(
        matches!(result, Err(InductiveError::ConstructorReturnType(_, _))),
        "Expected ConstructorReturnType, got {result:?}"
    );
}

/// Test deeply nested non-positive occurrence
#[test]
fn test_error_deeply_nested_non_positive() {
    // T : Type where mk : ((T → Nat) → Nat) → T
    // T appears in nested negative position
    let t = Name::from_string("T");
    let nat = Name::from_string("Nat");
    let t_ref = Expr::const_(t.clone(), vec![]);
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    // T → Nat (inner function)
    let inner = Expr::arrow(t_ref.clone(), nat_ref.clone());
    // (T → Nat) → Nat (middle)
    let middle = Expr::arrow(inner, nat_ref);
    // ((T → Nat) → Nat) → T (constructor type)
    let ctor_type = Expr::arrow(middle, t_ref);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: t.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("T.mk"),
                type_: ctor_type,
            }],
        }],
    };

    let result = validate_inductive(&decl);
    assert!(
        matches!(result, Err(InductiveError::NonPositive(ref name, ref culprit))
            if *name == t && *culprit == t),
        "Expected NonPositive for T, got {result:?}"
    );
}

// Note: The following InductiveError variants are defined but not currently
// returned by validate_inductive:
// - NoConstructors(Name) - could be added for types with no constructors
// - InvalidConstructorType(Name) - for malformed constructor types
// - InvalidType(String) - for general validation failures
// - UniverseMismatch(Name) - for universe inconsistencies
// - DuplicateConstructor(Name) - for duplicate constructor names
// - InvalidParams - for parameter validation
//
// These exist for future extensibility when validation is enhanced.

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proptest property tests for positivity checker
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// These supplement Kani harnesses that time out due to CBMC's exhaustive
// approach on check_positivity (Name::from_string + recursive matching
// cause state explosion). Proptest provides high-confidence randomized
// coverage of the same properties.

use proptest::prelude::*;

/// Strategy for generating "other" type names (not the inductive under test).
fn other_name_strategy() -> impl Strategy<Value = Name> {
    prop_oneof![
        Just(Name::from_string("X")),
        Just(Name::from_string("Y")),
        Just(Name::from_string("Z")),
        Just(Name::from_string("A")),
        Just(Name::from_string("Nat")),
    ]
}

/// Strategy for expressions that do NOT mention a given inductive name.
/// Used to build constructor types where certain subexpressions must be "clean".
fn expr_without_ind(depth: u32) -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![
        Just(Expr::prop()),
        Just(Expr::type_()),
        Just(Expr::from_kind(ExprKind::BVar(0))),
        other_name_strategy().prop_map(|n| Expr::const_(n, vec![])),
    ];
    if depth == 0 {
        leaf.boxed()
    } else {
        prop_oneof![
            leaf,
            expr_without_ind(depth - 1).prop_map(|e| {
                Expr::from_kind(ExprKind::Pi(
                    BinderInfo::Default.into(),
                    Arc::new(Expr::prop()),
                    Arc::new(e),
                ))
            }),
            (expr_without_ind(depth - 1), expr_without_ind(depth - 1)).prop_map(|(d, c)| {
                Expr::from_kind(ExprKind::Pi(
                    BinderInfo::Default.into(),
                    Arc::new(d),
                    Arc::new(c),
                ))
            }),
        ]
        .boxed()
    }
}

// ── Unit tests (converted from irrelevant proptests, #1346) ────────

/// Negative occurrence (T → Prop) → T is rejected.
/// The codomain of the inner Pi is irrelevant to the check — only T in
/// the domain of (T → _) triggers NonPositive. (ex-proptest #1)
#[test]
fn test_negative_occurrence_rejected() {
    let ind = Name::from_string("T");
    let t_const = Expr::const_(ind.clone(), vec![]);
    // (T → Prop) → T
    let inner = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_const.clone()),
        Arc::new(Expr::prop()),
    ));
    let ctor_type = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner),
        Arc::new(t_const),
    ));
    assert!(
        check_pos(&ind, &ctor_type, 0).is_err(),
        "Negative occurrence (T → _) → T must be rejected"
    );
}

/// Positive occurrence Ind → Ind → ... → Ind is accepted for depths 0-3.
/// Only 4 inputs exist (depth 0..4) so proptest adds no value. (ex-proptest #2)
#[test]
fn test_positive_occurrence_accepted_depth_0_to_3() {
    let ind = Name::from_string("Ind");
    let ind_const = Expr::const_(ind.clone(), vec![]);
    for depth in 0u32..4 {
        let mut ctor = ind_const.clone();
        for _ in 0..=depth {
            ctor = Expr::from_kind(ExprKind::Pi(
                BinderInfo::Default.into(),
                Arc::new(ind_const.clone()),
                Arc::new(ctor),
            ));
        }
        assert!(
            check_pos(&ind, &ctor, 0).is_ok(),
            "Direct positive occurrence at depth {depth} must be accepted"
        );
    }
}

/// Deeply nested negative ((T → Prop) → Prop) → T is rejected.
/// x and y are irrelevant — only T in domain of inner Pi matters. (ex-proptest #4)
#[test]
fn test_deeply_nested_negative_rejected() {
    let ind = Name::from_string("T");
    let t_const = Expr::const_(ind.clone(), vec![]);
    let prop = Expr::prop();
    // ((T → Prop) → Prop) → T
    let inner1 = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(t_const.clone()),
        Arc::new(prop.clone()),
    ));
    let inner2 = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner1),
        Arc::new(prop),
    ));
    let ctor_type = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(inner2),
        Arc::new(t_const),
    ));
    assert!(
        check_pos(&ind, &ctor_type, 0).is_err(),
        "Nested negative ((T → _) → _) → T must be rejected"
    );
}

/// Domain not mentioning T → T is always accepted. The `if !mentions_name()`
/// guard was dead because expr_without_ind guarantees no "T". Removed guard,
/// test directly asserts the property. (ex-proptest #6)
#[test]
fn test_no_mention_always_accepted() {
    let ind = Name::from_string("T");
    // Several domains that don't mention T
    let cases: Vec<Expr> = vec![
        Expr::prop(),
        Expr::type_(),
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(Expr::prop()),
            Arc::new(Expr::type_()),
        )),
    ];
    for domain in cases {
        assert!(!mentions_name(&domain, &ind), "domain should not mention T");
        let ctor_type = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(domain),
            Arc::new(Expr::const_(ind.clone(), vec![])),
        ));
        assert!(
            check_pos(&ind, &ctor_type, 0).is_ok(),
            "Domain not mentioning T → T must be accepted"
        );
    }
}

// ── Proptests that benefit from randomization ────────────────────────

proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(200))]

    /// Strictly positive nested (X → T) → T is accepted.
    /// Randomized `other` exercises different domain shapes in mentions_name.
    #[test]
    fn prop_strictly_positive_nested_accepted(
        other in expr_without_ind(2),
    ) {
        let ind = Name::from_string("T");
        let t_const = Expr::const_(ind.clone(), vec![]);

        // Build: (other → T) → T
        let inner = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(other),
            Arc::new(t_const.clone()),
        ));
        let ctor_type = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(inner),
            Arc::new(t_const),
        ));

        let result = check_pos(&ind, &ctor_type, 0);
        prop_assert!(result.is_ok(),
            "Strictly positive (X → T) → T must be accepted");
    }

    /// App(T, clean_arg) → T is accepted (T applied to args not mentioning T).
    /// Randomized `arg` exercises different app argument shapes.
    #[test]
    fn prop_app_inductive_clean_args_accepted(
        arg in expr_without_ind(1),
    ) {
        let ind = Name::from_string("T");
        let t_const = Expr::const_(ind.clone(), vec![]);

        let t_applied = Expr::from_kind(ExprKind::App(Arc::new(t_const.clone()), Arc::new(arg)));
        let ctor_type = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(t_applied),
            Arc::new(t_const),
        ));

        let result = check_pos(&ind, &ctor_type, 0);
        prop_assert!(result.is_ok(),
            "App(T, clean_arg) → T must be accepted");
    }

    /// Negative control: a checker that accepts everything would pass the
    /// positive tests above but fail here. Randomized domain containing T in
    /// negative position must be rejected. (#1346 acceptance criteria)
    #[test]
    fn prop_negative_with_varied_structure(
        wrapper in expr_without_ind(1),
    ) {
        let ind = Name::from_string("T");
        let t_const = Expr::const_(ind.clone(), vec![]);

        // Build: (T → wrapper) → T — T in domain of inner Pi = negative
        let inner = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(t_const.clone()),
            Arc::new(wrapper),
        ));
        let ctor_type = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(inner),
            Arc::new(t_const),
        ));

        let result = check_pos(&ind, &ctor_type, 0);
        prop_assert!(result.is_err(),
            "Negative (T → _) → T must be rejected regardless of codomain shape");
    }
}

/// Mutual inductive with sibling in positive (codomain) position of a
/// higher-order constructor argument is valid.
///
/// A.mk : (Nat → B) → A should be accepted because B appears to the RIGHT
/// of the inner arrow (positive position). This exercises the Pi codomain
/// branch in check_strictly_positive_impl.
#[test]
fn test_positivity_mutual_codomain_positive() {
    let (a, b) = (Name::from_string("A"), Name::from_string("B"));
    let (a_ref, b_ref) = (
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    // A.mk : (Nat → B) → A — B in codomain of inner arrow = positive
    let a_mk = Expr::arrow(Expr::arrow(nat_ref, b_ref.clone()), a_ref.clone());
    // B.mk : B (nullary)
    let b_mk = b_ref.clone();
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    validate_inductive(&decl)
        .expect("B in positive (codomain) position of inner arrow should pass");
}

/// Lean 4 calls whnf before positivity checking (inductive.cpp:394).
/// clean does NOT — positivity is checked on raw expression structure.
///
/// A Let binding that hides a negative occurrence will not be caught:
///   let T := (Foo → Nat) in (T → Foo) unfolds to ((Foo → Nat) → Foo)
///   which has Foo in negative position, but without whnf on the Let body
///   check_positivity only sees BVar(0) → Foo which appears clean.
///
/// This test documents the gap for tracking purposes. When whnf is added
/// to check_positivity_in_ctor_type_impl, this test should be inverted
/// (change expect to expect_err).
#[test]
fn test_positivity_let_hides_negative_occurrence_gap() {
    let foo = Name::from_string("Foo");
    let foo_ref = Expr::const_(foo.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let t_name = Name::from_string("T");

    // T := (Foo → Nat)
    let t_def = Expr::arrow(foo_ref.clone(), nat_ref.clone());
    let t_ref = Expr::bvar(0); // de Bruijn index 0 refers to the Let binding

    // Ctor type: let T := (Foo → Nat) in (T → Foo)
    // After substitution this is ((Foo → Nat) → Foo) which has Foo in
    // the domain of an inner arrow (negative). But without whnf on the
    // Let, check_positivity only sees BVar(0) → Foo.
    let _ = t_name; // Expr::let_ uses Name::anon() internally
    let ctor_type = Expr::let_named(
        Name::anon(),
        nat_ref, // type annotation
        t_def,
        Expr::arrow(t_ref, foo_ref.clone()),
        false,
    );

    // Without whnf, this PASSES despite the hidden negative occurrence.
    // This documents the gap vs Lean 4 (inductive.cpp:394 calls whnf first).
    let result = check_pos(&foo, &ctor_type, 0);
    assert!(
        result.is_ok(),
        "Without whnf, Let-hidden negative occurrence is not detected (known gap)"
    );
}

// ============================================================================
// Constructor return type parameter validation (#3241)
// ============================================================================

/// Valid parameterized inductive: constructor return type params match declared params.
///
/// MyList (A : Type) : Type
/// MyList.nil  : {A : Type} -> MyList A
/// MyList.cons : {A : Type} -> A -> MyList A -> MyList A
#[test]
fn test_validate_inductive_param_match_valid_list() {
    let list_name = Name::from_string("MyList");
    let list_ref = Expr::const_(list_name.clone(), vec![]);

    // MyList.nil : Pi (A : Type) . MyList A
    // In De Bruijn: Pi (_ : Type) . App(Const("MyList"), BVar(0))
    let nil_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(list_ref.clone(), Expr::bvar(0)),
    );

    // MyList.cons : Pi (A : Type) (x : A) (xs : MyList A) . MyList A
    // In De Bruijn: Pi (_ : Type) (_ : BVar(0)) (_ : App(Const("MyList"), BVar(1))) .
    //                App(Const("MyList"), BVar(2))
    let cons_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // x : A (A is BVar(0) under 1 binder)
            Expr::pi(
                BinderInfo::Default,
                Expr::app(list_ref.clone(), Expr::bvar(1)), // xs : MyList A (A is BVar(1) under 2 binders)
                Expr::app(list_ref.clone(), Expr::bvar(2)), // return: MyList A (A is BVar(2) under 3 binders)
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: list_name.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyList.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("MyList.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    validate_inductive(&decl).expect("Valid parameterized inductive should pass");
}

/// Invalid: constructor return type uses wrong parameter (constant instead of BVar).
///
/// BadList (A : Type) : Type
/// BadList.mk : {A : Type} -> BadList Nat   -- uses Nat instead of A
#[test]
fn test_validate_inductive_param_mismatch_const_instead_of_bvar() {
    let list_name = Name::from_string("BadList");
    let list_ref = Expr::const_(list_name.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // BadList.mk : Pi (A : Type) . BadList Nat
    // In De Bruijn: Pi (_ : Type) . App(Const("BadList"), Const("Nat"))
    // The return type arg is Const("Nat") instead of BVar(0) -- INVALID
    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(list_ref.clone(), nat_ref),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: list_name.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("BadList.mk"),
                type_: mk_type,
            }],
        }],
    };
    let err = validate_inductive(&decl).expect_err("Mismatched param should be rejected");
    assert!(
        matches!(
            err,
            InductiveError::ConstructorParamMismatch {
                ref ctor_name,
                ref ind_name,
                param_idx: 0,
            } if *ctor_name == Name::from_string("BadList.mk")
              && *ind_name == Name::from_string("BadList")
        ),
        "Expected ConstructorParamMismatch at param 0, got {err:?}"
    );
}

/// Invalid: constructor return type uses wrong BVar (points to wrong binder).
///
/// BadPair (A : Type) (B : Type) : Type
/// BadPair.mk : {A : Type} -> {B : Type} -> A -> B -> BadPair B A   -- swapped!
#[test]
fn test_validate_inductive_param_mismatch_swapped_bvars() {
    let pair_name = Name::from_string("BadPair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);

    // BadPair.mk : Pi (A : Type) (B : Type) (a : A) (b : B) . BadPair B A
    // In De Bruijn with 4 binders: A=BVar(3), B=BVar(2), a=BVar(1), b=BVar(0)
    // Correct return: App(App(Const("BadPair"), BVar(3)), BVar(2))
    // Swapped return: App(App(Const("BadPair"), BVar(2)), BVar(3))
    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    // Return: BadPair B A (swapped -- B at param 0, A at param 1)
                    Expr::app(
                        Expr::app(pair_ref.clone(), Expr::bvar(2)), // B instead of A
                        Expr::bvar(3),                              // A instead of B
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::arrow(Expr::type_(), Expr::type_())),
            constructors: vec![Constructor {
                name: Name::from_string("BadPair.mk"),
                type_: mk_type,
            }],
        }],
    };
    let err = validate_inductive(&decl).expect_err("Swapped params should be rejected");
    assert!(
        matches!(
            err,
            InductiveError::ConstructorParamMismatch { param_idx: 0, .. }
        ),
        "Expected ConstructorParamMismatch at param 0 (first mismatched), got {err:?}"
    );
}

/// Valid: no-param inductive passes (regression: ensure num_params=0 still works).
#[test]
fn test_validate_inductive_zero_params_still_valid() {
    let nat = Name::from_string("Nat2");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat2.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat2.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    validate_inductive(&decl).expect("Zero-param inductive should still pass");
}

/// Invalid: constructor return type has too few args for declared params.
///
/// BadType (A : Type) : Type
/// BadType.mk : {A : Type} -> BadType   -- missing parameter argument entirely
#[test]
fn test_validate_inductive_param_mismatch_missing_arg() {
    let name = Name::from_string("BadType");
    let type_ref = Expr::const_(name.clone(), vec![]);

    // BadType.mk : Pi (A : Type) . BadType   (no args applied)
    let mk_type = Expr::pi(BinderInfo::Implicit, Expr::type_(), type_ref.clone());

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("BadType.mk"),
                type_: mk_type,
            }],
        }],
    };
    let err = validate_inductive(&decl).expect_err("Missing param arg should be rejected");
    assert!(
        matches!(
            err,
            InductiveError::ConstructorParamMismatch { param_idx: 0, .. }
        ),
        "Expected ConstructorParamMismatch at param 0, got {err:?}"
    );
}

// ============================================================================
// Constructor return type index argument validation (#3243)
// ============================================================================

/// Index argument that mentions the inductive type should be rejected.
///
/// BadVec (n : Nat) : Type
/// BadVec.mk : {n : Nat} -> BadVec (BadVec n)   -- index mentions BadVec
///
/// Lean 4 rejects this via `!has_ind_occ(args[i])` for index args
/// (kernel/inductive.cpp:351-356, lean4#2125).
#[test]
fn test_validate_inductive_index_arg_mentions_inductive_rejected() {
    let badvec = Name::from_string("BadVec");
    let badvec_ref = Expr::const_(badvec.clone(), vec![]);
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    // BadVec.mk : Pi (n : Nat) . BadVec (BadVec n)
    // Return type: App(Const("BadVec"), App(Const("BadVec"), BVar(0)))
    // The index argument is App(Const("BadVec"), BVar(0)) which mentions BadVec
    let mk_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::app(
            badvec_ref.clone(),
            Expr::app(badvec_ref.clone(), Expr::bvar(0)),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: badvec.clone(),
            type_: Expr::arrow(nat_ref, Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("BadVec.mk"),
                type_: mk_type,
            }],
        }],
    };
    let err =
        validate_inductive(&decl).expect_err("Index arg mentioning inductive should be rejected");
    assert!(
        matches!(
            err,
            InductiveError::IndexArgMentionsInductive {
                ref ctor_name,
                ref ind_name,
                index_pos: 0,
            } if *ctor_name == Name::from_string("BadVec.mk")
              && *ind_name == badvec
        ),
        "Expected IndexArgMentionsInductive at index 0, got {err:?}"
    );
}

/// Valid indexed inductive: index argument does NOT mention the inductive type.
///
/// Vec (A : Type) : Nat -> Type
/// Vec.nil  : {A : Type} -> Vec A 0
/// Vec.cons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (succ n)
///
/// The index arguments (0 and succ n) don't mention Vec, so this is valid.
#[test]
fn test_validate_inductive_index_arg_clean_accepted() {
    let vec_name = Name::from_string("Vec");
    let vec_ref = Expr::const_(vec_name.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero_ref = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_ref = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // Vec.nil : Pi (A : Type) . Vec A 0
    // De Bruijn: Pi (_ : Type) . App(App(Const("Vec"), BVar(0)), Const("Nat.zero"))
    let nil_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(Expr::app(vec_ref.clone(), Expr::bvar(0)), zero_ref),
    );

    // Vec.cons : Pi (A : Type) (n : Nat) (x : A) (xs : Vec A n) . Vec A (succ n)
    // De Bruijn under 4 binders: A=BVar(3), n=BVar(2), x=BVar(1), xs=BVar(0)
    let cons_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            nat_ref.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // x : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::app(vec_ref.clone(), Expr::bvar(2)), Expr::bvar(1)), // xs : Vec A n
                    // Return: Vec A (succ n)
                    Expr::app(
                        Expr::app(vec_ref.clone(), Expr::bvar(3)), // Vec A
                        Expr::app(succ_ref, Expr::bvar(2)),        // succ n
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: vec_name.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::arrow(nat_ref, Expr::type_())),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Vec.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("Vec.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    validate_inductive(&decl).expect("Valid Vec with clean index args should pass");
}

/// Mutual inductive: index argument of one type mentions sibling type.
///
/// A : Nat -> Type
/// B : Type
/// A.mk : B -> A B    -- index is B (a sibling inductive type), should be rejected
/// B.mk : B
#[test]
fn test_validate_inductive_index_arg_mentions_mutual_sibling_rejected() {
    let a = Name::from_string("A");
    let b = Name::from_string("B");
    let a_ref = Expr::const_(a.clone(), vec![]);
    let b_ref = Expr::const_(b.clone(), vec![]);

    // A.mk : B -> A B
    // Return type is App(Const("A"), Const("B")) — index arg is Const("B")
    let a_mk = Expr::arrow(b_ref.clone(), Expr::app(a_ref.clone(), b_ref.clone()));
    // B.mk : B (nullary)
    let b_mk = b_ref.clone();

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::arrow(Expr::type_(), Expr::type_()),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    let result = validate_inductive(&decl);
    assert!(
        result.is_err(),
        "Mutual sibling type B in index arg of A should be rejected (#3243)"
    );
    assert!(
        matches!(
            result,
            Err(InductiveError::IndexArgMentionsInductive {
                ref ind_name,
                index_pos: 0,
                ..
            }) if *ind_name == b
        ),
        "Expected IndexArgMentionsInductive with B at index 0, got {result:?}"
    );
}

/// No-index inductive (like Nat) should not be affected by the index check.
#[test]
fn test_validate_inductive_no_indices_unaffected() {
    let nat = Name::from_string("Nat3");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat3.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat3.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    validate_inductive(&decl).expect("No-index inductive should be unaffected by index check");
}

/// Parameterized inductive with clean index args passes.
///
/// MyFin (n : Nat) : Type
/// MyFin.zero : {n : Nat} -> MyFin (succ n)
/// MyFin.succ : {n : Nat} -> MyFin n -> MyFin (succ n)
///
/// Index arg `succ n` mentions Nat.succ but not MyFin — should pass.
#[test]
fn test_validate_inductive_parameterized_clean_index_passes() {
    let fin = Name::from_string("MyFin");
    let fin_ref = Expr::const_(fin.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let succ_ref = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // MyFin.zero : Pi (n : Nat) . MyFin (succ n)
    let zero_type = Expr::pi(
        BinderInfo::Implicit,
        nat_ref.clone(),
        Expr::app(fin_ref.clone(), Expr::app(succ_ref.clone(), Expr::bvar(0))),
    );

    // MyFin.succ : Pi (n : Nat) (x : MyFin n) . MyFin (succ n)
    let succ_type = Expr::pi(
        BinderInfo::Implicit,
        nat_ref.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(fin_ref.clone(), Expr::bvar(0)), // x : MyFin n
            Expr::app(fin_ref.clone(), Expr::app(succ_ref, Expr::bvar(1))), // MyFin (succ n)
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: fin.clone(),
            type_: Expr::arrow(nat_ref, Expr::type_()),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyFin.zero"),
                    type_: zero_type,
                },
                Constructor {
                    name: Name::from_string("MyFin.succ"),
                    type_: succ_type,
                },
            ],
        }],
    };
    validate_inductive(&decl).expect("MyFin with clean index args should pass");
}

/// Valid multi-parameter inductive: Prod (A : Type) (B : Type) : Type
/// Prod.mk : {A : Type} -> {B : Type} -> A -> B -> Prod A B
///
/// Verifies that BVar indices are correctly computed for multi-parameter types:
/// Under 4 binders (A, B, a, b), param A = BVar(3), param B = BVar(2).
#[test]
fn test_validate_inductive_multi_param_prod_valid() {
    let prod = Name::from_string("Prod");
    let prod_ref = Expr::const_(prod.clone(), vec![]);

    // Prod.mk : Pi (A : Type) (B : Type) (a : A) (b : B) . Prod A B
    // Under 4 binders: A=BVar(3), B=BVar(2), a=BVar(1), b=BVar(0)
    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    // Return: Prod A B = App(App(Const("Prod"), BVar(3)), BVar(2))
                    Expr::app(
                        Expr::app(prod_ref.clone(), Expr::bvar(3)), // A
                        Expr::bvar(2),                              // B
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: prod.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::arrow(Expr::type_(), Expr::type_())),
            constructors: vec![Constructor {
                name: Name::from_string("Prod.mk"),
                type_: mk_type,
            }],
        }],
    };
    validate_inductive(&decl).expect("Valid 2-param Prod should pass");
}

/// Invalid: second parameter is wrong BVar while first is correct.
///
/// BadProd (A : Type) (B : Type) : Type
/// BadProd.mk : {A : Type} -> {B : Type} -> A -> B -> BadProd A A  -- B replaced with A
///
/// Verifies param_idx reports index 1 (the second param) as the mismatch.
#[test]
fn test_validate_inductive_param_mismatch_second_param_wrong() {
    let prod = Name::from_string("BadProd2");
    let prod_ref = Expr::const_(prod.clone(), vec![]);

    // BadProd2.mk : Pi (A : Type) (B : Type) (a : A) (b : B) . BadProd2 A A
    // Under 4 binders: A=BVar(3), B=BVar(2)
    // Correct return: App(App(Const, BVar(3)), BVar(2))
    // Wrong return:   App(App(Const, BVar(3)), BVar(3))  -- second param is A instead of B
    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    Expr::app(
                        Expr::app(prod_ref.clone(), Expr::bvar(3)), // A -- correct
                        Expr::bvar(3), // A instead of B (BVar(3) instead of BVar(2)) -- WRONG
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: prod.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::arrow(Expr::type_(), Expr::type_())),
            constructors: vec![Constructor {
                name: Name::from_string("BadProd2.mk"),
                type_: mk_type,
            }],
        }],
    };
    let err = validate_inductive(&decl).expect_err("Second param mismatch should be rejected");
    assert!(
        matches!(
            err,
            InductiveError::ConstructorParamMismatch { param_idx: 1, .. }
        ),
        "Expected ConstructorParamMismatch at param_idx 1 (second param), got {err:?}"
    );
}

/// Valid: parameterized inductive with both params and indices.
///
/// HVec (A : Type) : Nat -> Type
/// HVec.nil : {A : Type} -> HVec A 0
/// HVec.cons : {A : Type} -> {n : Nat} -> A -> HVec A n -> HVec A (succ n)
///
/// Param A at index 0 must be correct BVar; index args (0, succ n) are free.
#[test]
fn test_validate_inductive_param_and_index_combined_valid() {
    let hvec = Name::from_string("HVec");
    let hvec_ref = Expr::const_(hvec.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero_ref = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_ref = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // HVec.nil : Pi (A : Type) . HVec A 0
    // Under 1 binder: A=BVar(0)
    let nil_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(Expr::app(hvec_ref.clone(), Expr::bvar(0)), zero_ref),
    );

    // HVec.cons : Pi (A : Type) (n : Nat) (x : A) (xs : HVec A n) . HVec A (succ n)
    // Under 4 binders: A=BVar(3), n=BVar(2), x=BVar(1), xs=BVar(0)
    let cons_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            nat_ref.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // x : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::app(hvec_ref.clone(), Expr::bvar(2)), Expr::bvar(1)),
                    // Return: HVec A (succ n)
                    Expr::app(
                        Expr::app(hvec_ref.clone(), Expr::bvar(3)), // param A
                        Expr::app(succ_ref.clone(), Expr::bvar(2)), // index (succ n)
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: hvec.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::arrow(nat_ref, Expr::type_())),
            constructors: vec![
                Constructor {
                    name: Name::from_string("HVec.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("HVec.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    validate_inductive(&decl).expect("HVec with correct param and clean index should pass");
}

/// Invalid: parameterized indexed inductive where the param is wrong.
///
/// BadHVec (A : Type) : Nat -> Type
/// BadHVec.mk : {A : Type} -> {n : Nat} -> BadHVec Nat n  -- Nat instead of A
///
/// The index (n) is fine, but param 0 is wrong (Const("Nat") instead of BVar).
#[test]
fn test_validate_inductive_param_wrong_with_valid_index() {
    let hvec = Name::from_string("BadHVec");
    let hvec_ref = Expr::const_(hvec.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // BadHVec.mk : Pi (A : Type) (n : Nat) . BadHVec Nat n
    // Under 2 binders: A=BVar(1), n=BVar(0)
    // Wrong: param 0 is Const("Nat") instead of BVar(1)
    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            nat_ref.clone(),
            Expr::app(
                Expr::app(hvec_ref.clone(), nat_ref.clone()), // Nat instead of BVar(1)
                Expr::bvar(0),                                // index n -- correct
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: hvec.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::arrow(nat_ref, Expr::type_())),
            constructors: vec![Constructor {
                name: Name::from_string("BadHVec.mk"),
                type_: mk_type,
            }],
        }],
    };
    let err =
        validate_inductive(&decl).expect_err("Wrong param with valid index should be rejected");
    assert!(
        matches!(
            err,
            InductiveError::ConstructorParamMismatch { param_idx: 0, .. }
        ),
        "Expected ConstructorParamMismatch at param 0, got {err:?}"
    );
}
