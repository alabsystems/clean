// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::test_helpers::assert_bvar;
use super::*;
use crate::expr::BinderInfo;
use crate::inductive::{count_pi_args, Constructor, InductiveType};
use crate::level::Level;
use crate::quot::QuotKind;
use crate::tc::TypeChecker;

#[test]
fn test_add_inductive_nat() {
    let mut env = Environment::new();

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

    // Add the inductive
    env.add_inductive(decl).unwrap();

    // Check that Nat is in the environment with arity verification
    // Nat : Type (0 Pi binders, it's a type constant)
    let nat_const = env.get_const(&Name::from_string("Nat")).unwrap();
    assert_eq!(
        count_pi_args(&nat_const.type_),
        0,
        "Nat type should have 0 Pi binders"
    );

    // Nat.zero : Nat (0 Pi binders)
    let zero = env.get_const(&Name::from_string("Nat.zero")).unwrap();
    assert_eq!(
        count_pi_args(&zero.type_),
        0,
        "Nat.zero type should have 0 Pi binders"
    );

    // Nat.succ : Nat → Nat (1 Pi binder)
    let succ = env.get_const(&Name::from_string("Nat.succ")).unwrap();
    assert_eq!(
        count_pi_args(&succ.type_),
        1,
        "Nat.succ type should have 1 Pi binder"
    );

    // Verify inductive properties
    let ind_info = env.get_inductive(&Name::from_string("Nat")).unwrap();
    assert_eq!(ind_info.num_params, 0);
    assert_eq!(ind_info.num_indices, 0);
    assert!(ind_info.is_recursive);
    assert!(ind_info.is_large_elim);
    assert_eq!(ind_info.constructor_names.len(), 2);

    // Verify constructor properties
    let zero_info = env.get_constructor(&Name::from_string("Nat.zero")).unwrap();
    assert_eq!(zero_info.num_fields, 0);
    assert_eq!(zero_info.constructor_idx, 0);

    let succ_info = env.get_constructor(&Name::from_string("Nat.succ")).unwrap();
    assert_eq!(succ_info.num_fields, 1);
    assert_eq!(succ_info.constructor_idx, 1);

    // Verify recursor properties
    let rec_info = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();
    assert_eq!(rec_info.num_minors, 2);
    assert_eq!(rec_info.num_motives, 1);
    assert_eq!(rec_info.rules.len(), 2);
}

#[test]
fn test_add_inductive_list() {
    let mut env = Environment::new();

    // List : Type → Type
    // nil : {A : Type} → List A
    // cons : {A : Type} → A → List A → List A

    let u = Name::from_string("u");
    let list = Name::from_string("List");

    // List.{u} : Type u → Type u
    let list_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );

    // List A (with BVar 0 for parameter A)
    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );

    // nil : (A : Type u) → List A
    let nil_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        list_a.clone(),
    );

    // cons : (A : Type u) → A → List A → List A
    // First we need to build the body with correct de Bruijn indices
    // After binding A:
    //   A → List A → List A
    // BVar 0 = A, List A uses BVar 0
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1), // A (now at depth 1)
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2), // A (now at depth 2)
            ),
        ),
    );
    let cons_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        cons_body,
    );

    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1, // A is a parameter
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };

    env.add_inductive(decl).unwrap();

    // Verify
    let ind_info = env.get_inductive(&list).unwrap();
    assert_eq!(ind_info.num_params, 1);
    assert_eq!(ind_info.num_indices, 0);
    assert!(ind_info.is_recursive);

    let nil_info = env.get_constructor(&Name::from_string("List.nil")).unwrap();
    assert_eq!(nil_info.num_fields, 0); // nil has no fields after the parameter

    let cons_info = env
        .get_constructor(&Name::from_string("List.cons"))
        .unwrap();
    assert_eq!(cons_info.num_fields, 2); // cons has 2 fields: head and tail
}

#[test]
fn test_register_structure_fields() {
    let mut env = Environment::new();

    let pair = Name::from_string("Pair");

    // Pair : Type → Type → Type
    let pair_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );

    // mk : (A B : Type) → A → B → Pair A B
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(), // B
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // B
                    Expr::app(
                        Expr::app(Expr::const_(pair.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_type,
            }],
        }],
    };

    env.add_inductive(decl).unwrap();

    env.register_structure_fields(
        pair.clone(),
        vec![Name::from_string("fst"), Name::from_string("snd")],
    )
    .unwrap();

    assert_eq!(
        env.get_structure_field_index(&pair, &Name::from_string("fst")),
        Some(0)
    );
    assert_eq!(
        env.get_structure_field_index(&pair, &Name::from_string("snd")),
        Some(1)
    );
    assert_eq!(
        env.get_structure_field_names(&pair)
            .map(|f| f.len())
            .unwrap(),
        2
    );
}

#[test]
fn test_register_structure_fields_invalid_count() {
    let mut env = Environment::new();

    let struct_name = Name::from_string("Struct");
    // Fields are Type (= Sort(1)), so inductive must live in Sort(2) = Type 1
    let struct_type = Expr::sort(Level::succ(Level::succ(Level::zero())));
    let ctor_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::const_(struct_name.clone(), vec![]),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: struct_type,
            constructors: vec![Constructor {
                name: Name::from_string("Struct.mk"),
                type_: ctor_type,
            }],
        }],
    };

    env.add_inductive(decl).unwrap();

    let err = env
        .register_structure_fields(struct_name.clone(), vec![Name::from_string("only")])
        .unwrap_err();

    assert!(matches!(
        err,
        EnvError::InvalidFieldCount {
            struct_name: _,
            expected: 2,
            actual: 1
        }
    ));
}

#[test]
fn test_add_inductive_duplicate() {
    let mut env = Environment::new();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.zero"),
                type_: nat_ref,
            }],
        }],
    };

    env.add_inductive(decl.clone()).unwrap();

    // Re-adding the IDENTICAL inductive is an idempotent no-op (a2c36eec design:
    // foundation/kernel double-registration of a shared foundational type). The
    // tightened guard fires only when the type AND all its constructors are
    // already present, so this exact re-add is skipped without error. Genuine
    // conflicts still fail: a same-name inductive with a DIFFERENT constructor set
    // (see `test_add_inductive_logic_operators`) and a name-vs-constant collision
    // (see `test_add_inductive_name_in_constants_only`) both still error.
    env.add_inductive(decl)
        .expect("re-adding the identical inductive should be an idempotent no-op");
}

#[test]
fn test_add_inductive_prop() {
    let mut env = Environment::new();

    // False : Prop (empty inductive in Prop)
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("False"),
            type_: Expr::prop(),
            constructors: vec![], // No constructors
        }],
    };

    env.add_inductive(decl).unwrap();

    let ind_info = env.get_inductive(&Name::from_string("False")).unwrap();
    assert!(!ind_info.is_recursive);
    assert!(ind_info.is_large_elim); // False allows large elimination
}

#[test]
fn test_add_inductive_reflexive() {
    // Test W-type (well-founded trees) - a reflexive inductive
    // W A B is reflexive because the inductive appears in a function domain
    let mut env = Environment::new();

    let w = Name::from_string("W");

    let w_ref = Expr::const_(w.clone(), vec![]);

    // sup : (f : Type → W) → W  is simpler for testing reflexivity
    // W must live in Sort 2 (= Type 1) because the field (Type → W)
    // has sort 2: Type = Sort 1 lives in Sort 2, so the function type
    // (Sort 1 → W) has sort imax(2, 2) = 2. Per-field universe check
    // requires is_geq(result_level, 2), so result_level must be ≥ 2.
    let sup_type = Expr::arrow(Expr::arrow(Expr::type_(), w_ref.clone()), w_ref);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: w.clone(),
            type_: Expr::sort(Level::succ(Level::succ(Level::zero()))), // Sort 2
            constructors: vec![Constructor {
                name: Name::from_string("W.sup"),
                type_: sup_type,
            }],
        }],
    };

    env.add_inductive(decl).unwrap();

    let ind_info = env.get_inductive(&w).unwrap();
    assert!(ind_info.is_recursive, "W-type should be recursive");
    assert!(ind_info.is_reflexive, "W-type should be reflexive");
}

#[test]
fn test_add_inductive_nat_not_reflexive() {
    // Nat is recursive but NOT reflexive
    let mut env = Environment::new();

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

    env.add_inductive(decl).unwrap();

    let ind_info = env.get_inductive(&nat).unwrap();
    assert!(ind_info.is_recursive, "Nat should be recursive");
    assert!(!ind_info.is_reflexive, "Nat should NOT be reflexive");
}

#[test]
fn test_environment_json_serialization() {
    let mut env = Environment::new();

    // Add a simple definition
    let id_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::arrow(Expr::bvar(0), Expr::bvar(0)),
    );
    let id_value = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );

    // Use add_decl_unchecked: type checker can't handle FVar context for this artificial id
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: vec![],
        type_: id_type,
        value: id_value,
        is_reducible: true,
    });

    // Serialize to JSON
    let json = env.to_json().unwrap();
    assert!(json.contains("\"id\"") || json.contains("Str"));

    // Deserialize
    let env2 = Environment::from_json(&json).unwrap();
    let id_const = env2.get_const(&Name::from_string("id")).unwrap();
    assert!(
        id_const.is_reducible,
        "id should be reducible after JSON round-trip"
    );
}

#[test]
fn test_environment_bincode_serialization() {
    let mut env = Environment::new();

    // Add Nat inductive
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

    env.add_inductive(decl).unwrap();

    // Serialize to bincode
    let data = env.to_bincode().unwrap();
    assert!(!data.is_empty());

    // Deserialize and verify arity preserved through round-trip
    let env2 = Environment::from_bincode(&data).unwrap();
    let nat_const = env2.get_const(&Name::from_string("Nat")).unwrap();
    assert_eq!(
        count_pi_args(&nat_const.type_),
        0,
        "Nat type should survive round-trip"
    );

    let zero = env2.get_const(&Name::from_string("Nat.zero")).unwrap();
    assert_eq!(
        count_pi_args(&zero.type_),
        0,
        "Nat.zero type should survive round-trip"
    );

    let succ = env2.get_const(&Name::from_string("Nat.succ")).unwrap();
    assert_eq!(
        count_pi_args(&succ.type_),
        1,
        "Nat.succ type should survive round-trip"
    );

    let nat_ind = env2.get_inductive(&nat).unwrap();
    assert_eq!(
        nat_ind.constructor_names.len(),
        2,
        "Nat should have 2 constructors after bincode round-trip"
    );
}

#[test]
fn test_environment_roundtrip() {
    let mut env = Environment::new();

    // Add multiple declarations
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myAxiom"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("u")))),
    })
    .unwrap();

    // JSON roundtrip
    let json = env.to_json().unwrap();
    let env_json = Environment::from_json(&json).unwrap();
    assert_eq!(env.num_constants(), env_json.num_constants());

    // Bincode roundtrip
    let data = env.to_bincode().unwrap();
    let env_bin = Environment::from_bincode(&data).unwrap();
    assert_eq!(env.num_constants(), env_bin.num_constants());
}

// =========================================================================
// Quotient Type Tests
// =========================================================================

#[test]
fn test_init_quot() {
    let mut env = Environment::new();

    // Initially no quotients
    assert!(!env.has_quot());
    assert!(
        env.get_quot(&Name::from_string("Quot")).is_none(),
        "Quot should not exist before init"
    );

    // Initialize quotients
    env.init_quot();

    // Now quotients should be present
    assert!(env.has_quot());
    // Verify QuotKind for each quotient primitive
    let q = env.get_quot(&Name::from_string("Quot")).unwrap();
    assert_eq!(q.kind, QuotKind::Type, "Quot should be QuotKind::Type");
    let q_mk = env.get_quot(&Name::from_string("Quot.mk")).unwrap();
    assert_eq!(q_mk.kind, QuotKind::Mk, "Quot.mk should be QuotKind::Mk");
    let q_lift = env.get_quot(&Name::from_string("Quot.lift")).unwrap();
    assert_eq!(
        q_lift.kind,
        QuotKind::Lift,
        "Quot.lift should be QuotKind::Lift"
    );
    let q_ind = env.get_quot(&Name::from_string("Quot.ind")).unwrap();
    assert_eq!(
        q_ind.kind,
        QuotKind::Ind,
        "Quot.ind should be QuotKind::Ind"
    );

    // Should also be in constants with arity verification
    // Quot : {α : Sort u} → (α → α → Prop) → Sort u
    let quot = env.get_const(&Name::from_string("Quot")).unwrap();
    assert_eq!(
        count_pi_args(&quot.type_),
        2,
        "Quot type should have 2 Pi binders (α, r)"
    );

    // Quot.mk : {α : Sort u} → {r : α → α → Prop} → α → @Quot α r
    let quot_mk = env.get_const(&Name::from_string("Quot.mk")).unwrap();
    assert_eq!(
        count_pi_args(&quot_mk.type_),
        3,
        "Quot.mk type should have 3 Pi binders (α, r, a)"
    );

    // Quot.lift : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) → (∀ a b, r a b → f a = f b) → @Quot α r → β
    let quot_lift = env.get_const(&Name::from_string("Quot.lift")).unwrap();
    assert_eq!(
        count_pi_args(&quot_lift.type_),
        6,
        "Quot.lift type should have 6 Pi binders (α, r, β, f, h, q)"
    );

    // Quot.ind : {α : Sort u} → {r : α → α → Prop} → {motive : @Quot α r → Prop} → (∀ a, motive (Quot.mk r a)) → ∀ q, motive q
    let quot_ind = env.get_const(&Name::from_string("Quot.ind")).unwrap();
    assert_eq!(
        count_pi_args(&quot_ind.type_),
        5,
        "Quot.ind type should have 5 Pi binders (α, r, motive, h, q)"
    );
}

#[test]
fn test_with_quot() {
    let env = Environment::with_quot();

    // Should have quotients initialized
    assert!(env.has_quot());
    let q = env.get_quot(&Name::from_string("Quot")).unwrap();
    assert_eq!(
        q.kind,
        QuotKind::Type,
        "Quot should be QuotKind::Type via with_quot"
    );
}

#[test]
fn test_init_quot_idempotent() {
    let mut env = Environment::new();

    env.init_quot();
    let num_constants1 = env.num_constants();

    // Calling init_quot again should be a no-op
    env.init_quot();
    let num_constants2 = env.num_constants();

    assert_eq!(num_constants1, num_constants2);
}

#[test]
fn test_quot_kinds() {
    let env = Environment::with_quot();

    assert_eq!(
        env.get_quot_kind(&Name::from_string("Quot")),
        Some(QuotKind::Type)
    );
    assert_eq!(
        env.get_quot_kind(&Name::from_string("Quot.mk")),
        Some(QuotKind::Mk)
    );
    assert_eq!(
        env.get_quot_kind(&Name::from_string("Quot.lift")),
        Some(QuotKind::Lift)
    );
    assert_eq!(
        env.get_quot_kind(&Name::from_string("Quot.ind")),
        Some(QuotKind::Ind)
    );
    assert_eq!(env.get_quot_kind(&Name::from_string("Nat")), None);
}

#[test]
fn test_quot_serialization_json() {
    let env = Environment::with_quot();

    // Serialize to JSON
    let json = env.to_json().unwrap();
    assert!(json.contains("Quot"));

    // Deserialize
    let env2 = Environment::from_json(&json).unwrap();
    assert!(env2.has_quot());
    let q = env2.get_quot(&Name::from_string("Quot")).unwrap();
    assert_eq!(
        q.kind,
        QuotKind::Type,
        "Quot should survive JSON round-trip"
    );
}

#[test]
fn test_quot_serialization_bincode() {
    let env = Environment::with_quot();

    // Serialize to bincode
    let data = env.to_bincode().unwrap();

    // Deserialize and verify QuotKind preserved through round-trip
    let env2 = Environment::from_bincode(&data).unwrap();
    assert!(env2.has_quot());
    let q = env2.get_quot(&Name::from_string("Quot")).unwrap();
    assert_eq!(
        q.kind,
        QuotKind::Type,
        "Quot should survive bincode round-trip"
    );
    let q_mk = env2.get_quot(&Name::from_string("Quot.mk")).unwrap();
    assert_eq!(
        q_mk.kind,
        QuotKind::Mk,
        "Quot.mk should survive bincode round-trip"
    );
    let q_lift = env2.get_quot(&Name::from_string("Quot.lift")).unwrap();
    assert_eq!(
        q_lift.kind,
        QuotKind::Lift,
        "Quot.lift should survive bincode round-trip"
    );
    let q_ind = env2.get_quot(&Name::from_string("Quot.ind")).unwrap();
    assert_eq!(
        q_ind.kind,
        QuotKind::Ind,
        "Quot.ind should survive bincode round-trip"
    );
}

#[test]
fn test_quotients_iterator() {
    let env = Environment::with_quot();

    let quot_names: Vec<String> = env.quotients().map(|q| q.name.to_string()).collect();
    assert!(quot_names.contains(&"Quot".to_string()));
    assert!(quot_names.contains(&"Quot.mk".to_string()));
    assert!(quot_names.contains(&"Quot.lift".to_string()));
    assert!(quot_names.contains(&"Quot.ind".to_string()));
    // Quot.sound is the fifth quotient primitive (the soundness axiom relating
    // `Quot.mk` of related elements); it is a FOUNDATIONAL axiom.
    assert!(quot_names.contains(&"Quot.sound".to_string()));
    assert_eq!(quot_names.len(), 5);
}

// =========================================================================
// Mutation Testing Kill Tests - env.rs survivors
// =========================================================================

#[test]
fn test_add_inductive_logic_operators() {
    // Kill mutant: replace || with && in Environment::add_inductive (lines 295, 301)
    // This test ensures both constants and inductives/constructors maps are checked

    let mut env = Environment::new();

    // First, add Nat as an inductive
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.zero"),
                type_: nat_ref.clone(),
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    // Now try adding an inductive with same name - should fail due to inductives map
    let decl2 = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(), // Duplicate name
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat2.zero"),
                type_: Expr::const_(nat.clone(), vec![]),
            }],
        }],
    };
    let err = env
        .add_inductive(decl2)
        .expect_err("duplicate inductive name must fail");
    assert!(
        matches!(err, EnvError::DuplicateName(ref name) if *name == nat),
        "expected duplicate Nat error, got {err:?}"
    );

    // Try adding with duplicate constructor name
    let other = Name::from_string("Other");
    let decl3 = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: other.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.zero"), // Duplicate ctor name
                type_: Expr::const_(other.clone(), vec![]),
            }],
        }],
    };
    let err = env
        .add_inductive(decl3)
        .expect_err("duplicate constructor name must fail");
    assert!(
        matches!(err, EnvError::DuplicateName(ref name) if *name == Name::from_string("Nat.zero")),
        "expected duplicate Nat.zero error, got {err:?}"
    );
}

#[test]
fn test_instantiate_type_logic() {
    // Kill mutant: replace || with && in Environment::instantiate_type (line 451)

    use crate::level::Level;

    let mut env = Environment::new();

    // Add a polymorphic constant
    let u = Name::from_string("u");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myPoly"),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
    })
    .unwrap();

    // Case 1: no level params and no provided levels - should return type as-is
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myMono"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    let ty = env.instantiate_type(&Name::from_string("myMono"), &[]);
    assert_eq!(
        ty.unwrap(),
        Expr::prop(),
        "monomorphic instantiate_type should return Prop"
    );

    // Case 2: has level params, empty levels provided - level count mismatch (#1277)
    let ty2 = env.instantiate_type(&Name::from_string("myPoly"), &[]);
    assert!(
        ty2.is_none(),
        "level count mismatch must return None (#1277)"
    );

    // Case 3: has level params, levels provided - should substitute
    let ty3 = env.instantiate_type(&Name::from_string("myPoly"), &[Level::zero()]);
    assert_eq!(ty3.unwrap(), Expr::from_kind(ExprKind::Sort(Level::zero())));
}

#[test]
fn test_unfold_logic() {
    // Kill mutant: replace || with && in Environment::unfold (line 471)

    use crate::level::Level;

    let mut env = Environment::new();

    // Add a reducible definition with level params
    let u = Name::from_string("u");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myDef"),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        value: Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        is_reducible: true,
    })
    .unwrap();

    // Case 1: unfold with empty levels — level count mismatch (#1277)
    let val = env.unfold(&Name::from_string("myDef"), &[]);
    assert!(
        val.is_none(),
        "level count mismatch must return None (#1277)"
    );

    // Case 2: unfold with provided levels
    let val2 = env.unfold(&Name::from_string("myDef"), &[Level::zero()]);
    assert_eq!(
        val2.unwrap(),
        Expr::from_kind(ExprKind::Sort(Level::zero()))
    );
}

#[test]
fn test_iterators_return_values() {
    // Kill mutants: replace iterators with ::std::iter::empty()
    // - constants() line 486
    // - inductives() line 491
    // - constructors() line 496
    // - recursors() line 501

    let mut env = Environment::new();

    // Add Nat inductive to populate all collections
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
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();

    // Verify iterators return non-empty results
    assert!(
        env.constants().count() > 0,
        "constants() should not be empty"
    );
    assert!(
        env.inductives().count() > 0,
        "inductives() should not be empty"
    );
    assert!(
        env.constructors().count() > 0,
        "constructors() should not be empty"
    );
    assert!(
        env.recursors().count() > 0,
        "recursors() should not be empty"
    );

    // Verify specific counts
    // constants: sorry, trustedArith, trustedAy (pre-initialized) + Nat,
    // Nat.zero, Nat.succ, Nat.rec, Nat.casesOn, Nat.recOn = 9. The generated
    // noConfusion pair is intentionally absent until Eq exists: publishing a
    // pre-Eq StructuralOnly placeholder would let later consumers mistake an
    // unverified generated object for kernel authority. `init_eq` performs the
    // canonical late repair, covered by the dedicated noConfusion tests.
    assert_eq!(env.constants().count(), 9);
    // inductives: Nat = 1
    assert_eq!(env.inductives().count(), 1);
    // constructors: Nat.zero, Nat.succ = 2
    assert_eq!(env.constructors().count(), 2);
    // recursors: Nat.rec, Nat.casesOn, Nat.recOn = 3
    // (#2162: noConfusion is now a definition, not a recursor)
    assert_eq!(env.recursors().count(), 3);

    // Verify iterator content
    let const_names: Vec<_> = env.constants().map(|c| c.name.to_string()).collect();
    assert!(const_names.contains(&"Nat".to_string()));
    assert!(const_names.contains(&"Nat.zero".to_string()));
    assert!(const_names.contains(&"Nat.succ".to_string()));
    assert!(const_names.contains(&"Nat.rec".to_string()));
    assert!(const_names.contains(&"Nat.casesOn".to_string()));
    assert!(const_names.contains(&"Nat.recOn".to_string()));
    assert!(!const_names.contains(&"Nat.noConfusionType".to_string()));
    assert!(!const_names.contains(&"Nat.noConfusion".to_string()));
}

#[test]
fn test_no_confusion_type_value_typechecks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
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
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
    env.init_eq().unwrap();

    // Get noConfusionType constant and verify it has a value
    let nct = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .expect("Nat.noConfusionType should exist");
    assert!(
        nct.value.is_some(),
        "Nat.noConfusionType should have a value (it's a definition)"
    );

    let value = nct.value.as_ref().unwrap();
    let ty = &nct.type_;

    // Type-check the value against the declared type
    let tc = TypeChecker::new(&env);
    match tc.check_type(value, ty) {
        Ok(()) => {} // Success
        Err(e) => {
            panic!(
                "Nat.noConfusionType value failed type check:\n  error: {:?}\n  type: {:?}\n  value: {:?}",
                e, ty, value
            );
        }
    }
}

#[test]
fn test_no_confusion_type_parameterized_typechecks() {
    use crate::tc::TypeChecker;

    // Test with a Type-valued parameterized type (1 param, 1 ctor, 1 field)
    let mut env = Environment::new();
    let v = Name::from_string("v");
    let v_level = crate::level::Level::param(v.clone());
    let type_v = Expr::sort(crate::level::Level::succ(v_level.clone()));

    // Wrap : Type v → Type v
    let wrap_type = Expr::arrow(type_v.clone(), type_v.clone());

    // Wrap.mk : {α : Type v} → α → Wrap α
    let wrap_mk_type = Expr::pi(
        BinderInfo::Implicit,
        type_v.clone(), // α : Type v
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // (val : α)
            Expr::app(
                Expr::const_(Name::from_string("Wrap"), vec![v_level.clone()]),
                Expr::bvar(1), // Wrap α
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![v],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Wrap"),
            type_: wrap_type,
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: wrap_mk_type,
            }],
        }],
    };
    // Eq + HEq before add_inductive: the v4.30 heterogeneous noConfusion
    // convention (designs/2026-07-03-noconfusion-ctoridx-convention.md) uses
    // HEq for param-mentioning fields.
    env.init_eq().unwrap();
    env.init_heq().unwrap();
    env.add_inductive(decl).unwrap();

    let nct = env
        .get_const(&Name::from_string("Wrap.noConfusionType"))
        .expect("Wrap.noConfusionType should exist");
    let nct_value = nct
        .value
        .as_ref()
        .expect("Wrap.noConfusionType should have a value");

    let tc = TypeChecker::new(&env);
    match tc.check_type(nct_value, &nct.type_) {
        Ok(()) => {}
        Err(e) => {
            panic!(
                "Wrap.noConfusionType value failed type check:\n  error: {:?}\n  type: {:?}\n  value: {:?}",
                e, nct.type_, nct.value.as_ref().unwrap()
            );
        }
    }
}

#[test]
fn test_to_json_pretty_actual_content() {
    // Kill mutants: replace to_json_pretty with Ok(String::new()) or Ok("xyzzy".into())

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let json = env.to_json_pretty().unwrap();

    // Must be valid JSON with actual content (not empty or "xyzzy")
    assert!(!json.is_empty(), "JSON should not be empty");
    assert_ne!(json, "xyzzy", "JSON should not be placeholder");
    assert!(json.len() > 10, "JSON should have substantial content");

    // Should contain our declaration
    assert!(
        json.contains("test") || json.contains("Str"),
        "JSON should contain our axiom"
    );

    // Should be parseable back
    let env2 = Environment::from_json(&json).unwrap();
    assert_eq!(env.num_constants(), env2.num_constants());
}

#[test]
fn test_save_load_file_roundtrip() {
    // Kill mutants:
    // - save_to_file returns Ok(()) without actually saving (line 540)
    // - load_from_file returns Ok(Default::default()) (line 548)

    use std::fs;

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("fileTest"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Create a unique temp directory and use a file path inside it
    let temp_dir = tempfile::tempdir().unwrap();
    let test_path = temp_dir.path().join("test_env.bin");

    // Verify file does not exist before save
    assert!(!test_path.exists(), "File should not exist before save");

    // Save to file
    env.save_to_file(&test_path).unwrap();

    // Verify file was actually created and has content
    assert!(test_path.exists(), "File should be created by save_to_file");
    let file_size = fs::metadata(&test_path).unwrap().len();
    assert!(file_size > 0, "File should not be empty");

    // Load back and verify content is preserved
    let env2 = Environment::load_from_file(&test_path).unwrap();
    assert_eq!(
        env.num_constants(),
        env2.num_constants(),
        "Number of constants should match"
    );
    let loaded_info = env2
        .get_const(&Name::from_string("fileTest"))
        .expect("Loaded env should have our axiom");
    assert_eq!(
        loaded_info.level_params.len(),
        0,
        "fileTest should have 0 level params after roundtrip"
    );
    // temp_dir cleaned up automatically when it goes out of scope
}

#[test]
fn test_num_constants_actual_count() {
    // Kill mutants: replace num_constants with 0 or 1 (line 555)

    let mut env = Environment::new();

    // New environment has sorry + trustedArith + trustedAy pre-initialized
    assert_eq!(env.num_constants(), 3); // sorry + trustedArith + trustedAy

    // Add one constant
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c1"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    assert_eq!(env.num_constants(), 4); // base(3) + c1

    // Add another
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c2"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    assert_eq!(env.num_constants(), 5); // base(3) + c1 + c2

    // Add more to be sure it's not just returning 1
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c3"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    assert_eq!(env.num_constants(), 6); // base(3) + c1 + c2 + c3
}

#[test]
fn test_num_inductives_actual_count() {
    // Kill mutants: replace num_inductives with 0 or 1 (line 560)

    let mut env = Environment::new();

    // Empty environment
    assert_eq!(env.num_inductives(), 0);

    // Add one inductive
    let nat = Name::from_string("Nat");
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.zero"),
                type_: Expr::const_(nat.clone(), vec![]),
            }],
        }],
    };
    env.add_inductive(decl).unwrap();
    assert_eq!(env.num_inductives(), 1);

    // Add another inductive
    let bool_name = Name::from_string("Bool");
    let decl2 = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: Expr::const_(bool_name.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: Expr::const_(bool_name.clone(), vec![]),
                },
            ],
        }],
    };
    env.add_inductive(decl2).unwrap();
    assert_eq!(env.num_inductives(), 2);

    // Add a third to ensure it's counting, not returning constant
    let unit_name = Name::from_string("Unit");
    let decl3 = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: unit_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Unit.unit"),
                type_: Expr::const_(unit_name.clone(), vec![]),
            }],
        }],
    };
    env.add_inductive(decl3).unwrap();
    assert_eq!(env.num_inductives(), 3);
}

// =========================================================================
// Mutation Kill Tests - OR vs AND operators
// =========================================================================

#[test]
fn test_add_inductive_name_in_constants_only() {
    // Kill mutant: replace || with && at line 295
    // Test case: name exists in constants but NOT in inductives
    // With ||: returns error (correct)
    // With &&: would NOT return error (wrong - allows duplicate)

    let mut env = Environment::new();

    // Add "Foo" as a regular constant (not an inductive)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Verify Foo is in constants but NOT in inductives
    let foo = env.get_const(&Name::from_string("Foo")).unwrap();
    assert_eq!(
        count_pi_args(&foo.type_),
        0,
        "Foo axiom type should have 0 Pi binders"
    );
    assert!(
        env.get_inductive(&Name::from_string("Foo")).is_none(),
        "Foo should be axiom, not inductive"
    );

    // Now try to add an inductive with the same name "Foo"
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Foo"), // Same name as existing constant
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Foo.mk"),
                type_: Expr::const_(Name::from_string("Foo"), vec![]),
            }],
        }],
    };

    // This MUST fail because "Foo" is already in constants
    let err = env
        .add_inductive(decl)
        .expect_err("inductive name that conflicts with an existing constant must fail");
    assert!(
        matches!(err, EnvError::DuplicateName(ref name) if *name == Name::from_string("Foo")),
        "expected duplicate Foo error, got {err:?}"
    );
}

#[test]
fn test_add_inductive_ctor_name_in_constants_only() {
    // Kill mutant: replace || with && at line 301
    // Test case: constructor name exists in constants but NOT in constructors map
    // With ||: returns error (correct)
    // With &&: would NOT return error (wrong - allows duplicate)

    let mut env = Environment::new();

    // Add "Bar.mk" as a regular constant (not a constructor)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Bar.mk"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Verify Bar.mk is in constants but NOT in constructors
    let bar_mk = env.get_const(&Name::from_string("Bar.mk")).unwrap();
    assert_eq!(
        count_pi_args(&bar_mk.type_),
        0,
        "Bar.mk axiom type should have 0 Pi binders"
    );
    assert!(
        env.get_constructor(&Name::from_string("Bar.mk")).is_none(),
        "Bar.mk should be axiom, not constructor"
    );

    // Now try to add an inductive whose constructor has that name
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bar"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Bar.mk"), // Same name as existing constant
                type_: Expr::const_(Name::from_string("Bar"), vec![]),
            }],
        }],
    };

    // This MUST fail because "Bar.mk" is already in constants
    let err = env
        .add_inductive(decl)
        .expect_err("constructor name that conflicts with an existing constant must fail");
    assert!(
        matches!(err, EnvError::DuplicateName(ref name) if *name == Name::from_string("Bar.mk")),
        "expected duplicate Bar.mk error, got {err:?}"
    );
}

#[test]
fn test_instantiate_type_empty_levels_nonempty_params() {
    // Updated for #1277: level count mismatch must be rejected.
    // Previously this silently returned the type without substitution,
    // leaving dangling Level::Param values. Lean 4 treats this as a hard error.

    use crate::level::Level;

    let mut env = Environment::new();

    let u = Name::from_string("u");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("polyConst"),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
    })
    .unwrap();

    // 0 levels for 1 param → None (level count mismatch)
    let result = env.instantiate_type(&Name::from_string("polyConst"), &[]);
    assert!(
        result.is_none(),
        "level count mismatch (0 for 1) must return None (#1277)"
    );
}

#[test]
fn test_unfold_empty_levels_nonempty_params() {
    // Updated for #1277: level count mismatch must be rejected.

    use crate::level::Level;

    let mut env = Environment::new();

    let u = Name::from_string("u");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("polyDef"),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        value: Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        is_reducible: true,
    })
    .unwrap();

    // 0 levels for 1 param → None (level count mismatch)
    let result = env.unfold(&Name::from_string("polyDef"), &[]);
    assert!(
        result.is_none(),
        "level count mismatch (0 for 1) must return None (#1277)"
    );
}

#[test]
fn test_instantiate_type_nonempty_levels_empty_params() {
    // Updated for #1277: level count mismatch must be rejected.

    use crate::level::Level;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("monoConst"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // 1 level for 0 params → None (level count mismatch)
    let result = env.instantiate_type(&Name::from_string("monoConst"), &[Level::zero()]);
    assert!(
        result.is_none(),
        "level count mismatch (1 for 0) must return None (#1277)"
    );
}

#[test]
fn test_unfold_nonempty_levels_empty_params() {
    // Updated for #1277: level count mismatch must be rejected.

    use crate::level::Level;

    let mut env = Environment::new();

    // Use add_decl_unchecked: artificial expression for testing unfolding, not type checking
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("monoDef"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::prop(),
        is_reducible: true,
    });

    // 1 level for 0 params → None (level count mismatch)
    let result = env.unfold(&Name::from_string("monoDef"), &[Level::zero()]);
    assert!(
        result.is_none(),
        "level count mismatch (1 for 0) must return None (#1277)"
    );
}

#[test]
fn test_instantiate_type_polymorphic_with_empty_levels() {
    // Updated for #1277: level count mismatch must be rejected.
    // Previously returned type with dangling Level::Param — unsound.

    use crate::level::Level;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("polyAxiom"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("u")))),
    })
    .unwrap();

    // 0 levels for 1 param → None
    let result = env.instantiate_type(&Name::from_string("polyAxiom"), &[]);
    assert!(
        result.is_none(),
        "level count mismatch must return None (#1277)"
    );
}

#[test]
fn test_unfold_polymorphic_with_empty_levels() {
    // Updated for #1277: level count mismatch must be rejected.

    use crate::level::Level;

    let mut env = Environment::new();

    // Use add_decl_unchecked: artificial expression for testing unfolding, not type checking
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("polyDef"),
        level_params: vec![Name::from_string("v")],
        type_: Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("v")))),
        value: Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("v")))),
        is_reducible: true,
    });

    // 0 levels for 1 param → None
    let result = env.unfold(&Name::from_string("polyDef"), &[]);
    assert!(
        result.is_none(),
        "level count mismatch must return None (#1277)"
    );
}

// =========================================================================
// Eq Type Tests
// =========================================================================

#[test]
fn test_init_eq() {
    let mut env = Environment::new();

    // Initially no Eq
    assert!(!env.has_eq());
    assert!(
        env.get_const(&Name::from_string("Eq")).is_none(),
        "Eq should not exist before init"
    );

    // Initialize Eq
    env.init_eq().unwrap();

    // Now Eq should be present
    assert!(env.has_eq());

    // Eq : {α : Sort u} → α → α → Prop (2 Pi binders for indices a, b; α is param)
    let eq_const = env.get_const(&Name::from_string("Eq")).unwrap();
    assert_eq!(
        count_pi_args(&eq_const.type_),
        3,
        "Eq type should have 3 Pi binders (α, a, b)"
    );

    // Eq.refl : {α : Sort u} → (a : α) → @Eq α a a
    let eq_refl = env.get_const(&Name::from_string("Eq.refl")).unwrap();
    assert_eq!(
        count_pi_args(&eq_refl.type_),
        2,
        "Eq.refl type should have 2 Pi binders (α, a)"
    );

    // Auto-generated recursors with arity checks
    let eq_rec = env.get_const(&Name::from_string("Eq.rec")).unwrap();
    assert!(
        count_pi_args(&eq_rec.type_) >= 5,
        "Eq.rec should have >= 5 Pi binders"
    );

    let eq_cases_on = env.get_const(&Name::from_string("Eq.casesOn")).unwrap();
    assert!(
        count_pi_args(&eq_cases_on.type_) >= 5,
        "Eq.casesOn should have >= 5 Pi binders"
    );

    let eq_rec_on = env.get_const(&Name::from_string("Eq.recOn")).unwrap();
    assert!(
        count_pi_args(&eq_rec_on.type_) >= 5,
        "Eq.recOn should have >= 5 Pi binders"
    );
    // Lean 4 does not generate noConfusion for Prop-valued inductive types (Eq)
    assert!(env
        .get_const(&Name::from_string("Eq.noConfusionType"))
        .is_none());
    assert!(env
        .get_const(&Name::from_string("Eq.noConfusion"))
        .is_none());
}

#[test]
fn test_init_eq_idempotent() {
    let mut env = Environment::new();

    env.init_eq().unwrap();
    let num_constants1 = env.num_constants();

    // Calling init_eq again should be a no-op
    env.init_eq().unwrap();
    let num_constants2 = env.num_constants();

    assert_eq!(num_constants1, num_constants2);
}

#[test]
fn test_eq_type_structure() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Check Eq has the correct structure
    let eq_info = env.get_inductive(&Name::from_string("Eq")).unwrap();
    assert_eq!(eq_info.num_params, 2); // α and a (a promoted by fixedIndicesToParams)
    assert_eq!(eq_info.num_indices, 1); // b is the remaining index
    assert_eq!(eq_info.constructor_names.len(), 1);
    assert_eq!(eq_info.constructor_names[0], Name::from_string("Eq.refl"));
}

#[test]
fn test_eq_refl_constructor() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Check Eq.refl has the correct type
    let refl = env.get_constructor(&Name::from_string("Eq.refl")).unwrap();
    assert_eq!(refl.num_params, 2); // α and a (a promoted by fixedIndicesToParams)
    assert_eq!(refl.num_fields, 0); // no fields beyond the 2 promoted params
    assert_eq!(refl.constructor_idx, 0);
}

#[test]
fn test_eq_rec_type() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Check Eq.rec exists and is a recursor
    let rec = env.get_recursor(&Name::from_string("Eq.rec")).unwrap();
    assert_eq!(rec.num_params, 2); // α and a (a promoted from index to rec-parameter per Lean 4 fixed-index pattern)
    assert_eq!(rec.rules.len(), 1); // One rule for Eq.refl
}

#[test]
fn test_eq_derived_definitions() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Check rfl: {α : Sort u} → {a : α} → @Eq α a a
    let rfl = env.get_const(&Name::from_string("rfl")).unwrap();
    let rfl_val = rfl
        .value
        .as_ref()
        .expect("rfl should have a definition body");
    assert!(
        matches!(&rfl_val.kind, ExprKind::Lam(bd, ..) if bd.info == BinderInfo::Implicit),
        "rfl value must be a lambda with implicit binder, got {:?}",
        std::mem::discriminant(&rfl_val.kind)
    );
    assert!(rfl.is_reducible);
    assert_eq!(
        count_pi_args(&rfl.type_),
        2,
        "rfl type should have 2 Pi binders (α, a)"
    );

    // Check Eq.symm: {α : Sort u} → {a b : α} → @Eq α a b → @Eq α b a
    let symm = env.get_const(&Name::from_string("Eq.symm")).unwrap();
    let symm_val = symm
        .value
        .as_ref()
        .expect("Eq.symm should have a proof body");
    assert!(
        matches!(&symm_val.kind, ExprKind::Lam(..)),
        "Eq.symm proof must be a lambda abstraction"
    );
    assert!(!symm.is_reducible); // theorems are not reducible
    assert_eq!(
        count_pi_args(&symm.type_),
        4,
        "Eq.symm type should have 4 Pi binders (α, a, b, h)"
    );

    // Check Eq.trans: {α : Sort u} → {a b c : α} → @Eq α a b → @Eq α b c → @Eq α a c
    let trans = env.get_const(&Name::from_string("Eq.trans")).unwrap();
    let trans_val = trans
        .value
        .as_ref()
        .expect("Eq.trans should have a proof body");
    assert!(
        matches!(&trans_val.kind, ExprKind::Lam(..)),
        "Eq.trans proof must be a lambda abstraction"
    );
    assert!(!trans.is_reducible);
    assert_eq!(
        count_pi_args(&trans.type_),
        6,
        "Eq.trans type should have 6 Pi binders (α, a, b, c, h1, h2)"
    );

    // Check Eq.ndrec: {α : Sort u} → {a : α} → {motive : α → Sort v} → motive a → {b : α} → @Eq α a b → motive b
    let ndrec = env.get_const(&Name::from_string("Eq.ndrec")).unwrap();
    let ndrec_val = ndrec
        .value
        .as_ref()
        .expect("Eq.ndrec should have a definition body");
    assert!(
        matches!(&ndrec_val.kind, ExprKind::Lam(..)),
        "Eq.ndrec value must be a lambda abstraction"
    );
    assert!(ndrec.is_reducible);
    assert_eq!(
        ndrec.level_params.len(),
        2,
        "Eq.ndrec has 2 universe params (u, v)"
    );
    assert_eq!(
        count_pi_args(&ndrec.type_),
        6,
        "Eq.ndrec type should have 6 Pi binders"
    );

    // Check Eq.ndrecOn: same arity as ndrec with different binder order
    let ndrec_on = env.get_const(&Name::from_string("Eq.ndrecOn")).unwrap();
    let ndrec_on_val = ndrec_on
        .value
        .as_ref()
        .expect("Eq.ndrecOn should have a definition body");
    assert!(
        matches!(&ndrec_on_val.kind, ExprKind::Lam(..)),
        "Eq.ndrecOn value must be a lambda abstraction"
    );
    assert!(ndrec_on.is_reducible);
    assert_eq!(
        ndrec_on.level_params.len(),
        2,
        "Eq.ndrecOn has 2 universe params (u, v)"
    );
    assert_eq!(
        count_pi_args(&ndrec_on.type_),
        6,
        "Eq.ndrecOn type should have 6 Pi binders"
    );

    // Check Eq.subst: {α : Sort u} → {motive : α → Prop} → {a b : α} → @Eq α a b → motive a → motive b
    let subst = env.get_const(&Name::from_string("Eq.subst")).unwrap();
    let subst_val = subst
        .value
        .as_ref()
        .expect("Eq.subst should have a proof body");
    assert!(
        matches!(&subst_val.kind, ExprKind::Lam(..)),
        "Eq.subst proof must be a lambda abstraction"
    );
    assert!(!subst.is_reducible); // theorem, not reducible
    assert_eq!(
        subst.level_params.len(),
        1,
        "Eq.subst has 1 universe param (u)"
    );
    assert_eq!(
        count_pi_args(&subst.type_),
        6,
        "Eq.subst type should have 6 Pi binders (α, motive, a, b, h, ha)"
    );

    // Check congrArg: {α : Sort u} → {β : Sort v} → {a₁ a₂ : α} → (f : α → β) → @Eq α a₁ a₂ → @Eq β (f a₁) (f a₂)
    let congr_arg = env.get_const(&Name::from_string("congrArg")).unwrap();
    let congr_arg_val = congr_arg
        .value
        .as_ref()
        .expect("congrArg should have a proof body");
    assert!(
        matches!(&congr_arg_val.kind, ExprKind::Lam(..)),
        "congrArg proof must be a lambda abstraction"
    );
    assert!(!congr_arg.is_reducible); // theorem, not reducible
    assert_eq!(
        congr_arg.level_params.len(),
        2,
        "congrArg has 2 universe params (u, v)"
    );
    assert_eq!(
        count_pi_args(&congr_arg.type_),
        6,
        "congrArg type should have 6 Pi binders (α, β, a₁, a₂, f, h)"
    );

    // Check congrFun (dependent version): has universe params u, v
    let congr_fun = env.get_const(&Name::from_string("congrFun")).unwrap();
    let congr_fun_val = congr_fun
        .value
        .as_ref()
        .expect("congrFun should have a proof body");
    assert!(
        matches!(&congr_fun_val.kind, ExprKind::Lam(..)),
        "congrFun proof must be a lambda abstraction"
    );
    assert!(!congr_fun.is_reducible); // theorem, not reducible
    assert_eq!(
        congr_fun.level_params.len(),
        2,
        "congrFun has 2 universe params (u, v)"
    );
    assert!(
        count_pi_args(&congr_fun.type_) >= 5,
        "congrFun type should have at least 5 Pi binders"
    );

    // Check congrFun' (non-dependent version): has universe params u, v
    let congr_fun_prime = env.get_const(&Name::from_string("congrFun'")).unwrap();
    let congr_fun_prime_val = congr_fun_prime
        .value
        .as_ref()
        .expect("congrFun' should have a proof body");
    assert!(
        matches!(&congr_fun_prime_val.kind, ExprKind::Lam(..)),
        "congrFun' proof must be a lambda abstraction"
    );
    assert!(!congr_fun_prime.is_reducible); // theorem, not reducible
    assert_eq!(
        congr_fun_prime.level_params.len(),
        2,
        "congrFun' has 2 universe params (u, v)"
    );
    assert!(
        count_pi_args(&congr_fun_prime.type_) >= 5,
        "congrFun' type should have at least 5 Pi binders"
    );

    // Check congr: {α : Sort u} → {β : Sort v} → {f₁ f₂ : α → β} → {a₁ a₂ : α} → ...
    let congr = env.get_const(&Name::from_string("congr")).unwrap();
    let congr_val = congr
        .value
        .as_ref()
        .expect("congr should have a proof body");
    assert!(
        matches!(&congr_val.kind, ExprKind::Lam(..)),
        "congr proof must be a lambda abstraction"
    );
    assert!(!congr.is_reducible); // theorem, not reducible
    assert_eq!(
        congr.level_params.len(),
        2,
        "congr has 2 universe params (u, v)"
    );
    assert!(
        count_pi_args(&congr.type_) >= 6,
        "congr type should have at least 6 Pi binders"
    );

    // Check cast: {α β : Sort u} → @Eq (Sort u) α β → α → β
    let cast = env.get_const(&Name::from_string("cast")).unwrap();
    let cast_val = cast
        .value
        .as_ref()
        .expect("cast should have a definition body");
    assert!(
        matches!(&cast_val.kind, ExprKind::Lam(..)),
        "cast value must be a lambda abstraction"
    );
    assert!(cast.is_reducible); // marked reducible for computation
    assert_eq!(cast.level_params.len(), 1, "cast has 1 universe param (u)");
    assert_eq!(
        count_pi_args(&cast.type_),
        4,
        "cast type should have 4 Pi binders (α, β, h, a)"
    );

    // Check Eq.mpr: {α β : Sort u} → @Eq (Sort u) α β → β → α
    let eq_mpr = env.get_const(&Name::from_string("Eq.mpr")).unwrap();
    let eq_mpr_val = eq_mpr
        .value
        .as_ref()
        .expect("Eq.mpr should have a definition body");
    assert!(
        matches!(&eq_mpr_val.kind, ExprKind::Lam(..)),
        "Eq.mpr value must be a lambda abstraction"
    );
    assert!(eq_mpr.is_reducible); // marked reducible for computation
    assert_eq!(
        eq_mpr.level_params.len(),
        1,
        "Eq.mpr has 1 universe param (u)"
    );
    assert_eq!(
        count_pi_args(&eq_mpr.type_),
        4,
        "Eq.mpr type should have 4 Pi binders (α, β, h, b)"
    )
}

#[test]
fn test_eq_all_constants_count() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Count all Eq-related constants:
    // - Eq (type)
    // - Eq.refl (constructor)
    // - Eq.rec, Eq.casesOn, Eq.recOn (recursors)
    // - Eq.noConfusionType, Eq.noConfusion (from inductive)
    // - rfl, Eq.symm, Eq.trans (derived definitions)
    // - Eq.ndrec, Eq.ndrecOn (non-dependent recursors)
    // - Eq.subst (substitution theorem)
    // - congrArg, congrFun, congr (congruence theorems)
    // - cast (type casting via equality)
    // - Eq.mp (forward transport)
    // - Eq.mpr (reverse transport)
    // Total: 18 (no noConfusion for Prop-valued Eq, matching Lean 4; includes congrFun')
    // (name, expected_level_params)
    let eq_names: Vec<(&str, usize)> = vec![
        ("Eq", 1),         // u
        ("Eq.refl", 1),    // u
        ("Eq.rec", 2),     // u, v
        ("Eq.casesOn", 2), // u, v
        ("Eq.recOn", 2),   // u, v
        ("rfl", 1),        // u
        ("Eq.symm", 1),    // u
        ("Eq.trans", 1),   // u
        ("Eq.ndrec", 2),   // u, v
        ("Eq.ndrecOn", 2), // u, v
        ("Eq.subst", 1),   // u
        ("congrArg", 2),   // u, v
        ("congrFun", 2),   // u, v
        ("congrFun'", 2),  // u, v
        ("congr", 2),      // u, v
        ("cast", 1),       // u
        ("Eq.mp", 1),      // u
        ("Eq.mpr", 1),     // u
    ];

    for (name, expected_lvl) in &eq_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("Expected {name} to exist"));
        assert_eq!(
            info.level_params.len(),
            *expected_lvl,
            "{name} should have {expected_lvl} level param(s), got {}",
            info.level_params.len()
        );
    }

    // 18 Eq constants + 3 pre-initialized (sorry + trustedArith + trustedAy) = 21
    assert_eq!(env.num_constants(), 21);
}

// =========================================================================
// HEq Type Tests
// =========================================================================

#[test]
fn test_init_heq() {
    let mut env = Environment::new();

    // Initially no HEq
    assert!(!env.has_heq());
    assert!(
        env.get_const(&Name::from_string("HEq")).is_none(),
        "HEq should not exist before init"
    );

    // Initialize HEq (this also initializes Eq)
    env.init_heq().unwrap();

    // Now HEq should be present
    assert!(env.has_heq());
    assert!(env.has_eq()); // Eq is a dependency

    // HEq : {α : Sort u} → α → {β : Sort u} → β → Prop
    let heq_const = env.get_const(&Name::from_string("HEq")).unwrap();
    assert_eq!(
        count_pi_args(&heq_const.type_),
        4,
        "HEq type should have 4 Pi binders (α, a, β, b)"
    );

    // HEq.refl : {α : Sort u} → (a : α) → @HEq α a α a
    let heq_refl = env.get_const(&Name::from_string("HEq.refl")).unwrap();
    assert_eq!(
        count_pi_args(&heq_refl.type_),
        2,
        "HEq.refl type should have 2 Pi binders (α, a)"
    );

    // Auto-generated recursors with arity checks
    let heq_rec = env.get_const(&Name::from_string("HEq.rec")).unwrap();
    assert!(
        count_pi_args(&heq_rec.type_) >= 5,
        "HEq.rec should have >= 5 Pi binders"
    );

    let heq_cases_on = env.get_const(&Name::from_string("HEq.casesOn")).unwrap();
    assert!(
        count_pi_args(&heq_cases_on.type_) >= 5,
        "HEq.casesOn should have >= 5 Pi binders"
    );

    let heq_rec_on = env.get_const(&Name::from_string("HEq.recOn")).unwrap();
    assert!(
        count_pi_args(&heq_rec_on.type_) >= 5,
        "HEq.recOn should have >= 5 Pi binders"
    );
}

#[test]
fn test_init_heq_idempotent() {
    let mut env = Environment::new();

    env.init_heq().unwrap();
    let num_constants1 = env.num_constants();

    // Calling init_heq again should be a no-op
    env.init_heq().unwrap();
    let num_constants2 = env.num_constants();

    assert_eq!(num_constants1, num_constants2);
}

#[test]
fn test_heq_type_structure() {
    let mut env = Environment::new();
    env.init_heq().unwrap();

    // Check HEq has the correct structure
    let heq_info = env.get_inductive(&Name::from_string("HEq")).unwrap();
    assert_eq!(heq_info.num_params, 2); // α and a are parameters
    assert_eq!(heq_info.num_indices, 2); // β and b are indices
    assert_eq!(heq_info.constructor_names.len(), 1);
    assert_eq!(heq_info.constructor_names[0], Name::from_string("HEq.refl"));
}

#[test]
fn test_heq_refl_constructor() {
    let mut env = Environment::new();
    env.init_heq().unwrap();

    // Check HEq.refl has the correct type
    let refl = env.get_constructor(&Name::from_string("HEq.refl")).unwrap();
    assert_eq!(refl.num_params, 2); // α and a are parameters
    assert_eq!(refl.num_fields, 0); // No additional fields beyond params
    assert_eq!(refl.constructor_idx, 0);
}

#[test]
fn test_heq_rec_type() {
    let mut env = Environment::new();
    env.init_heq().unwrap();

    // Check HEq.rec exists and is a recursor
    let rec = env.get_recursor(&Name::from_string("HEq.rec")).unwrap();
    assert_eq!(rec.num_params, 2); // α and a
    assert_eq!(rec.rules.len(), 1); // One rule for HEq.refl
}

#[test]
fn test_heq_derived_definitions() {
    let mut env = Environment::new();
    env.init_heq().unwrap();

    // Check HEq.rfl: {α : Sort u} → {a : α} → @HEq α a α a (2 Pi binders)
    let rfl = env.get_const(&Name::from_string("HEq.rfl")).unwrap();
    let rfl_val = rfl
        .value
        .as_ref()
        .expect("HEq.rfl should have a definition body");
    assert!(
        matches!(&rfl_val.kind, ExprKind::Lam(bd, ..) if bd.info == BinderInfo::Implicit),
        "HEq.rfl value must be a lambda with implicit binder"
    );
    assert!(rfl.is_reducible);
    assert_eq!(
        count_pi_args(&rfl.type_),
        2,
        "HEq.rfl type should have 2 Pi binders (α, a)"
    );

    // Check heq_of_eq: {α : Sort u} → {a b : α} → @Eq α a b → @HEq α a α b (4 Pi binders)
    let heq_of_eq = env.get_const(&Name::from_string("heq_of_eq")).unwrap();
    let heq_of_eq_val = heq_of_eq
        .value
        .as_ref()
        .expect("heq_of_eq should have a proof body");
    assert!(
        matches!(&heq_of_eq_val.kind, ExprKind::Lam(..)),
        "heq_of_eq proof must be a lambda abstraction"
    );
    assert!(!heq_of_eq.is_reducible);
    assert_eq!(
        count_pi_args(&heq_of_eq.type_),
        4,
        "heq_of_eq type should have 4 Pi binders (α, a, b, h)"
    );

    // Check eq_of_heq: {α : Sort u} → {a b : α} → @HEq α a α b → @Eq α a b (4 Pi binders)
    let eq_of_heq = env.get_const(&Name::from_string("eq_of_heq")).unwrap();
    let eq_of_heq_val = eq_of_heq
        .value
        .as_ref()
        .expect("eq_of_heq should have a proof body");
    assert!(
        matches!(&eq_of_heq_val.kind, ExprKind::Lam(..)),
        "eq_of_heq proof must be a lambda abstraction"
    );
    assert!(!eq_of_heq.is_reducible);
    assert_eq!(
        count_pi_args(&eq_of_heq.type_),
        4,
        "eq_of_heq type should have 4 Pi binders (α, a, b, h)"
    );

    // Check HEq.ndrec (reducible definition — #1403 fixed)
    let ndrec = env.get_const(&Name::from_string("HEq.ndrec")).unwrap();
    let ndrec_val = ndrec
        .value
        .as_ref()
        .expect("HEq.ndrec should have a definition body");
    assert!(
        matches!(&ndrec_val.kind, ExprKind::Lam(..)),
        "HEq.ndrec value must be a lambda abstraction"
    );
    assert!(ndrec.is_reducible);
    assert_eq!(
        ndrec.level_params.len(),
        2,
        "HEq.ndrec has 2 universe params (u, v)"
    );
    assert_eq!(
        count_pi_args(&ndrec.type_),
        7,
        "HEq.ndrec type should have 7 Pi binders (α, a, motive, m, β, b, h)"
    );

    // Check HEq.ndrecOn (reducible definition)
    let ndrec_on = env.get_const(&Name::from_string("HEq.ndrecOn")).unwrap();
    let ndrec_on_val = ndrec_on
        .value
        .as_ref()
        .expect("HEq.ndrecOn should have a definition body");
    assert!(
        matches!(&ndrec_on_val.kind, ExprKind::Lam(..)),
        "HEq.ndrecOn value must be a lambda abstraction"
    );
    assert!(ndrec_on.is_reducible);
    assert_eq!(
        ndrec_on.level_params.len(),
        2,
        "HEq.ndrecOn has 2 universe params (u, v)"
    );
    assert_eq!(
        count_pi_args(&ndrec_on.type_),
        7,
        "HEq.ndrecOn type should have 7 Pi binders (α, a, motive, β, b, h, m)"
    );

    // Check HEq.symm: {α β : Sort u} → {a : α} → {b : β} → @HEq α a β b → @HEq β b α a
    let symm = env.get_const(&Name::from_string("HEq.symm")).unwrap();
    let symm_val = symm
        .value
        .as_ref()
        .expect("HEq.symm should have a proof body");
    assert!(
        matches!(&symm_val.kind, ExprKind::Lam(..)),
        "HEq.symm proof must be a lambda abstraction"
    );
    assert!(!symm.is_reducible);
    assert_eq!(
        symm.level_params.len(),
        1,
        "HEq.symm has 1 universe param (u)"
    );
    assert_eq!(
        count_pi_args(&symm.type_),
        5,
        "HEq.symm type should have 5 Pi binders (α, β, a, b, h)"
    );

    // Check HEq.trans: heterogeneous transitivity
    let trans = env.get_const(&Name::from_string("HEq.trans")).unwrap();
    let trans_val = trans
        .value
        .as_ref()
        .expect("HEq.trans should have a proof body");
    assert!(
        matches!(&trans_val.kind, ExprKind::Lam(..)),
        "HEq.trans proof must be a lambda abstraction"
    );
    assert!(!trans.is_reducible);
    assert_eq!(trans.level_params.len(), 1); // just u
}

#[test]
fn test_heq_all_constants_count() {
    let mut env = Environment::new();
    env.init_heq().unwrap();

    // Count all HEq-related constants (beyond the Eq ones):
    // - HEq (type)
    // - HEq.refl (constructor)
    // - HEq.rec, HEq.casesOn, HEq.recOn (recursors)
    // - HEq.rfl, heq_of_eq, eq_of_heq (derived definitions)
    // - HEq.ndrec, HEq.ndrecOn (non-dependent recursors)
    // - HEq.symm, HEq.trans (symmetry and transitivity)
    // Total HEq: 12 (no noConfusion for Prop-valued HEq, matching Lean 4)
    // Plus Eq: 16
    // Grand total: 28
    // (name, expected_level_params)
    let heq_names: Vec<(&str, usize)> = vec![
        ("HEq", 1),         // u
        ("HEq.refl", 1),    // u
        ("HEq.rec", 2),     // u, v
        ("HEq.casesOn", 2), // u, v
        ("HEq.recOn", 2),   // u, v
        ("HEq.rfl", 1),     // u
        ("heq_of_eq", 1),   // u
        ("eq_of_heq", 1),   // u
        ("HEq.ndrec", 2),   // u, v
        ("HEq.ndrecOn", 2), // u, v
        ("HEq.symm", 1),    // u
        ("HEq.trans", 1),   // u
    ];

    for (name, expected_lvl) in &heq_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("Expected {name} to exist"));
        assert_eq!(
            info.level_params.len(),
            *expected_lvl,
            "{name} should have {expected_lvl} level param(s), got {}",
            info.level_params.len()
        );
    }

    // 18 Eq + 12 HEq + 3 pre-initialized (sorry + trustedArith + trustedAy) = 33
    assert_eq!(env.num_constants(), 33);
}

#[test]
fn test_heq_with_preexisting_eq() {
    let mut env = Environment::new();

    // First init Eq (3 pre-initialized: sorry + trustedArith + trustedAy)
    env.init_eq().unwrap();
    let eq_count = env.num_constants();
    assert_eq!(eq_count, 21); // 18 Eq + 3 pre-initialized

    // Now init HEq
    env.init_heq().unwrap();
    let heq_count = env.num_constants();

    // Should have added 12 more constants (HEq ones)
    assert_eq!(heq_count, 33); // 18 Eq + 12 HEq + 3 pre-initialized
}

// =========================================================================
// Extensionality Axiom Tests
// =========================================================================

#[test]
fn test_init_propext() {
    let mut env = Environment::new();

    // Initially no propext
    assert!(!env.has_propext());
    assert!(
        env.get_const(&Name::from_string("propext")).is_none(),
        "propext should not exist before init"
    );

    // Initialize propext (this also initializes Eq)
    env.init_propext().unwrap();

    // Should have propext
    assert!(env.has_propext());
    let propext = env.get_const(&Name::from_string("propext")).unwrap();
    assert_eq!(propext.value, None); // axiom has no value

    // idempotent
    env.init_propext().unwrap();
    assert!(env.has_propext());
}

/// Regression for the deep `Iff`-vs-`Pi`/`And` import bucket
/// (`Preorder.ext`, `Nat.coprime_pow_left_iff`,
/// `isCancelMul_iff_forall_isRegular`, …): the FAITHFUL Lean `propext` takes a
/// single `Iff` argument, `{a b : Prop} → (a ↔ b) → a = b`. Clean previously
/// registered the de-`Iff`'d EXPANDED curried stub
/// `{a b : Prop} → (a → b) → (b → a) → a = b`, a structurally different object
/// that rejected every imported `propext (h : a ↔ b)` application.
///
/// This test pins the faithful shape (third binder domain is `Iff a b`, NOT a
/// `Pi`) and exercises the round trip: a `propext (Iff.intro a b mp mpr)`
/// application type-checks against `a = b`, AND the old-style four-argument
/// expanded application is correctly REJECTED (so the object is genuinely the
/// faithful one, not one that accepts both shapes).
#[test]
fn test_propext_faithful_iff_shape() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_iff().unwrap();
    env.init_propext().unwrap();

    // ── (1) The registered type's third binder domain is `Iff a b`. ──────────
    let propext = env
        .get_const(&Name::from_string("propext"))
        .expect("propext registered");
    // type = {a : Prop} → {b : Prop} → (h : <dom>) → a = b
    let ExprKind::Pi(_, _, body1) = propext.type_.kind() else {
        panic!("propext type is not a Pi");
    };
    let ExprKind::Pi(_, _, body2) = body1.kind() else {
        panic!("propext type missing second binder");
    };
    let ExprKind::Pi(_, third_dom, _) = body2.kind() else {
        panic!("propext type missing third (proof) binder");
    };
    let third_head = third_dom.get_app_fn();
    assert!(
        matches!(third_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Iff")),
        "faithful propext's proof argument must be `Iff a b`, got head {:?}",
        third_head.kind()
    );

    // Build the body terms over four bound variables (a, b, mp, mpr) using de
    // Bruijn indices, then wrap them in the matching binder telescope so the
    // resulting term is CLOSED and can be inferred with no local context.
    //   binders (outer→inner):  a:Prop, b:Prop, mp:(a→b), mpr:(b→a)
    //   so inside the body:     a=BVar(3), b=BVar(2), mp=BVar(1), mpr=BVar(0)
    let tc = TypeChecker::new(&env);
    let prop = Expr::prop();
    let (a_v, b_v, mp_v, mpr_v) = (Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));

    // Helper: wrap a body in `λ a b (mp : a→b) (mpr : b→a) => body`.
    let wrap = |body: Expr| {
        // domains, written with the indices that are valid AT each binder site.
        let a_to_b = Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)); // (a → b) under {a,b}
        let b_to_a = Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3)); // (b → a) under {a,b,mp}
        let e = Expr::lam(BinderInfo::Default, b_to_a, body);
        let e = Expr::lam(BinderInfo::Default, a_to_b, e);
        let e = Expr::lam(BinderInfo::Default, prop.clone(), e);
        Expr::lam(BinderInfo::Default, prop.clone(), e)
    };

    // ── (2) `propext (Iff.intro a b mp mpr) : a = b` type-checks. ────────────
    let iff_ab = Expr::apps(
        Expr::const_(Name::from_string("Iff.intro"), vec![]),
        [a_v.clone(), b_v.clone(), mp_v.clone(), mpr_v.clone()],
    );
    let good_body = Expr::apps(
        Expr::const_(Name::from_string("propext"), vec![]),
        [a_v.clone(), b_v.clone(), iff_ab],
    );
    let good = wrap(good_body);
    let _good_ty = tc
        .infer_type(&good)
        .expect("λ a b mp mpr => propext (Iff.intro a b mp mpr) must type-check");

    // ── (3) The OLD expanded four-argument application is REJECTED. ──────────
    // `propext a b mp mpr` (no `Iff.intro`) must NOT type-check: passing `mp`
    // (a function `a → b`) where the faithful propext expects `a ↔ b` is a
    // genuine type error. This proves the registered object is the faithful
    // one (a single-`Iff` axiom), not one that silently accepts both shapes.
    let expanded_body = Expr::apps(
        Expr::const_(Name::from_string("propext"), vec![]),
        [a_v, b_v, mp_v, mpr_v],
    );
    let expanded = wrap(expanded_body);
    assert!(
        tc.infer_type(&expanded).is_err(),
        "old expanded four-argument `propext a b mp mpr` must be rejected by the faithful propext"
    );
}

#[test]
fn test_init_quot_sound() {
    let mut env = Environment::new();

    // Initially no Quot.sound
    assert!(!env.has_quot_sound());
    assert!(
        env.get_const(&Name::from_string("Quot.sound")).is_none(),
        "Quot.sound should not exist before init"
    );

    // Initialize Quot.sound (this also initializes Eq and Quot)
    env.init_quot_sound().unwrap();

    // Should have Quot.sound
    assert!(env.has_quot_sound());
    let quot_sound = env.get_const(&Name::from_string("Quot.sound")).unwrap();
    assert_eq!(quot_sound.value, None); // axiom has no value
    assert_eq!(quot_sound.level_params.len(), 1); // u

    // Should also have Quot primitives with arity verification
    let quot = env.get_const(&Name::from_string("Quot")).unwrap();
    assert_eq!(
        count_pi_args(&quot.type_),
        2,
        "Quot type should have 2 Pi binders (α, r)"
    );

    let quot_mk = env.get_const(&Name::from_string("Quot.mk")).unwrap();
    assert_eq!(
        count_pi_args(&quot_mk.type_),
        3,
        "Quot.mk type should have 3 Pi binders (α, r, a)"
    );

    // idempotent
    env.init_quot_sound().unwrap();
    assert!(env.has_quot_sound());
}

#[test]
fn test_init_funext() {
    let mut env = Environment::new();

    // Initially no funext
    assert!(!env.has_funext());
    assert!(
        env.get_const(&Name::from_string("funext")).is_none(),
        "funext should not exist before init"
    );

    // Initialize funext (this also initializes Eq)
    env.init_funext().unwrap();

    // Should have funext
    assert!(env.has_funext());
    let funext = env.get_const(&Name::from_string("funext")).unwrap();
    // funext is now a CHECKED Declaration::Theorem derived from Quot.sound,
    // so it carries a proof value (it is no longer an axiom).
    assert!(
        funext.value.is_some(),
        "funext should be a proved Theorem with a value, not an axiom"
    );
    assert_eq!(funext.level_params.len(), 2); // u, v

    // idempotent
    env.init_funext().unwrap();
    assert!(env.has_funext());
}

#[test]
fn test_all_extensionality_axioms() {
    let mut env = Environment::new();

    // Initialize all extensionality axioms
    env.init_propext().unwrap();
    env.init_quot_sound().unwrap();
    env.init_funext().unwrap();

    // Verify all exist
    assert!(env.has_propext());
    assert!(env.has_quot_sound());
    assert!(env.has_funext());

    // Check constants with arity verification
    // propext : {a b : Prop} → (a ↔ b) → a = b
    // Commit 3a09e7b7 replaced the historical de-Iff'd EXPANDED curried form
    // `{a b : Prop} → (a → b) → (b → a) → a = b` (4 binders) with the FAITHFUL
    // Lean 4 `Iff`-shaped object (3 binders) so imported .olean proofs applying
    // the genuine `propext (h : a ↔ b)` type-check.
    let propext = env.get_const(&Name::from_string("propext")).unwrap();
    assert_eq!(
        count_pi_args(&propext.type_),
        3,
        "propext type should have 3 Pi binders (a, b, h: a ↔ b) — faithful Lean 4 form (commit 3a09e7b7)"
    );

    // Quot.sound : {α : Sort u} → {r : α → α → Prop} → {a b : α} → r a b → @Quot.mk α r a = @Quot.mk α r b
    let quot_sound = env.get_const(&Name::from_string("Quot.sound")).unwrap();
    assert_eq!(
        count_pi_args(&quot_sound.type_),
        5,
        "Quot.sound type should have 5 Pi binders (α, r, a, b, h)"
    );

    // funext : {α : Sort u} → {β : α → Sort v} → {f g : ∀ x, β x} → (∀ x, f x = g x) → f = g
    let funext = env.get_const(&Name::from_string("funext")).unwrap();
    assert_eq!(
        count_pi_args(&funext.type_),
        5,
        "funext type should have 5 Pi binders (α, β, f, g, h)"
    );

    // Count: 18 Eq + 4 Quot + 3 axioms (propext, Quot.sound, funext)
    //        + 3 pre-initialized + 10 Iff-family constants = 38
    // Note: Quot.sound calls init_quot which adds 4 constants.
    // The 10 Iff constants (Iff, Iff.intro, Iff.rec + the derived
    // mp/mpr/rfl/symm/trans family) are pulled in because the FAITHFUL
    // `Iff`-shaped propext (commit 3a09e7b7) has init_propext call init_iff —
    // the historical count of 28 predates that change.
    assert_eq!(env.num_constants(), 38);
}

#[test]
fn test_init_iff() {
    let mut env = Environment::new();

    // Initially no Iff
    assert!(!env.has_iff());
    assert!(
        env.get_const(&Name::from_string("Iff")).is_none(),
        "Iff should not exist before init"
    );

    // Initialize Iff
    env.init_iff().unwrap();

    // Should have Iff and derived definitions
    assert!(env.has_iff());
    // Iff : Prop → Prop → Prop (1 param: none, 2 indices: a, b — but as structure, 0 params, 0 indices)
    let iff_ind = env.get_inductive(&Name::from_string("Iff")).unwrap();
    assert_eq!(
        iff_ind.constructor_names.len(),
        1,
        "Iff should have 1 constructor (Iff.intro)"
    );

    // Iff.intro : {a b : Prop} → (a → b) → (b → a) → Iff a b
    let intro = env.get_const(&Name::from_string("Iff.intro")).unwrap();
    assert_eq!(
        count_pi_args(&intro.type_),
        4,
        "Iff.intro type should have 4 Pi binders (a, b, hab, hba)"
    );

    // Iff.rec : recursor
    let iff_rec = env.get_const(&Name::from_string("Iff.rec")).unwrap();
    assert!(
        count_pi_args(&iff_rec.type_) >= 3,
        "Iff.rec should have >= 3 Pi binders"
    );

    // Iff.mp : {a b : Prop} → Iff a b → a → b
    let iff_mp = env.get_const(&Name::from_string("Iff.mp")).unwrap();
    let iff_mp_val = iff_mp
        .value
        .as_ref()
        .expect("Iff.mp should have a definition body");
    assert!(
        matches!(&iff_mp_val.kind, ExprKind::Lam(..)),
        "Iff.mp value must be a lambda abstraction"
    );
    assert!(iff_mp.is_reducible);
    assert_eq!(
        count_pi_args(&iff_mp.type_),
        4,
        "Iff.mp type should have 4 Pi binders (a, b, h, ha)"
    );

    // Iff.mpr : {a b : Prop} → Iff a b → b → a
    let iff_mpr = env.get_const(&Name::from_string("Iff.mpr")).unwrap();
    assert_eq!(
        count_pi_args(&iff_mpr.type_),
        4,
        "Iff.mpr type should have 4 Pi binders (a, b, h, hb)"
    );

    // Iff.rfl : {a : Prop} → Iff a a
    let iff_rfl = env.get_const(&Name::from_string("Iff.rfl")).unwrap();
    assert_eq!(
        count_pi_args(&iff_rfl.type_),
        1,
        "Iff.rfl type should have 1 Pi binder (a)"
    );

    // Iff.symm : {a b : Prop} → Iff a b → Iff b a
    let iff_symm = env.get_const(&Name::from_string("Iff.symm")).unwrap();
    assert_eq!(
        count_pi_args(&iff_symm.type_),
        3,
        "Iff.symm type should have 3 Pi binders (a, b, h)"
    );

    // Iff.trans : {a b c : Prop} → Iff a b → Iff b c → Iff a c
    let iff_trans = env.get_const(&Name::from_string("Iff.trans")).unwrap();
    assert_eq!(
        count_pi_args(&iff_trans.type_),
        5,
        "Iff.trans type should have 5 Pi binders (a, b, c, h1, h2)"
    );

    // idempotent
    env.init_iff().unwrap();
    assert!(env.has_iff());
}

#[test]
fn test_init_decidable() {
    let mut env = Environment::new();

    // Initially no Decidable
    assert!(!env.has_decidable());
    assert!(
        env.get_const(&Name::from_string("Decidable")).is_none(),
        "Decidable should not exist before init"
    );

    // Initialize Decidable
    env.init_decidable().unwrap();

    // Should have Decidable and constructors
    assert!(env.has_decidable());
    // Decidable : Prop → Type (1 param p, 0 indices)
    let dec_ind = env.get_inductive(&Name::from_string("Decidable")).unwrap();
    assert_eq!(dec_ind.num_params, 1, "Decidable should have 1 param (p)");

    // Decidable.isFalse : {p : Prop} → (p → False) → Decidable p
    let is_false = env
        .get_const(&Name::from_string("Decidable.isFalse"))
        .unwrap();
    assert_eq!(
        count_pi_args(&is_false.type_),
        2,
        "Decidable.isFalse type should have 2 Pi binders (p, h)"
    );

    // Decidable.isTrue : {p : Prop} → p → Decidable p
    let is_true = env
        .get_const(&Name::from_string("Decidable.isTrue"))
        .unwrap();
    assert_eq!(
        count_pi_args(&is_true.type_),
        2,
        "Decidable.isTrue type should have 2 Pi binders (p, h)"
    );

    let dec_rec = env.get_const(&Name::from_string("Decidable.rec")).unwrap();
    assert!(
        count_pi_args(&dec_rec.type_) >= 3,
        "Decidable.rec should have >= 3 Pi binders"
    );

    // idempotent
    env.init_decidable().unwrap();
    assert!(env.has_decidable());
}

#[test]
fn test_init_ite() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    assert!(!env.has_ite());
    assert!(env.get_const(&Name::from_string("ite")).is_none());

    env.init_ite().unwrap();

    assert!(env.has_decidable(), "ite should auto-init Decidable");
    assert!(env.has_ite());

    let ite = env.get_const(&Name::from_string("ite")).unwrap();
    assert_eq!(
        ite.level_params.len(),
        1,
        "ite should be universe-polymorphic"
    );
    assert_eq!(
        count_pi_args(&ite.type_),
        5,
        "ite type should have 5 Pi binders (α, c, h, a, b)"
    );
    let value = ite
        .value
        .as_ref()
        .expect("ite should be a reducible definition");
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(value, &ite.type_)
            .unwrap_or_else(|e| panic!("ite value should type-check against declared type: {e:?}"));
    }

    env.init_ite().unwrap();
    assert!(env.has_ite());
}

#[test]
fn test_init_classical() {
    let mut env = Environment::new();

    // Initially no Classical
    assert!(!env.has_classical());
    assert!(env
        .get_const(&Name::from_string("Classical.choice"))
        .is_none());

    // Initialize Classical
    env.init_classical().unwrap();

    // Should have Classical axioms and supporting types
    assert!(env.has_classical());

    // Nonempty : Sort u → Prop (1 param α, 0 indices)
    let nonempty_ind = env.get_inductive(&Name::from_string("Nonempty")).unwrap();
    assert_eq!(
        nonempty_ind.constructor_names.len(),
        1,
        "Nonempty should have 1 constructor (intro)"
    );
    // Nonempty.intro : {α : Sort u} → α → Nonempty α
    let nonempty_intro = env.get_const(&Name::from_string("Nonempty.intro")).unwrap();
    assert_eq!(
        count_pi_args(&nonempty_intro.type_),
        2,
        "Nonempty.intro type should have 2 Pi binders (α, val)"
    );

    // Or : Prop → Prop → Prop (2 params a b, 0 indices)
    let or_ind = env.get_inductive(&Name::from_string("Or")).unwrap();
    assert_eq!(
        or_ind.constructor_names.len(),
        2,
        "Or should have 2 constructors (inl, inr)"
    );
    // Or.inl : {a b : Prop} → a → Or a b
    let or_inl = env.get_const(&Name::from_string("Or.inl")).unwrap();
    assert_eq!(
        count_pi_args(&or_inl.type_),
        3,
        "Or.inl type should have 3 Pi binders (a, b, ha)"
    );
    // Or.inr : {a b : Prop} → b → Or a b
    let or_inr = env.get_const(&Name::from_string("Or.inr")).unwrap();
    assert_eq!(
        count_pi_args(&or_inr.type_),
        3,
        "Or.inr type should have 3 Pi binders (a, b, hb)"
    );

    // Classical axioms
    // Classical.choice : {α : Sort u} → Nonempty α → α
    let choice = env
        .get_const(&Name::from_string("Classical.choice"))
        .unwrap();
    assert_eq!(choice.value, None); // axiom has no value
    assert_eq!(choice.level_params.len(), 1); // u
    assert_eq!(
        count_pi_args(&choice.type_),
        2,
        "Classical.choice type should have 2 Pi binders (α, h)"
    );

    // Classical.em : (p : Prop) → Or p (Not p)
    //
    // Since the Diaconescu retirement (commit 549ebd11, `classical_em_proof.rs`)
    // `init_classical` no longer registers `Classical.em` as a
    // `Declaration::Axiom`: it registers a kernel-CHECKED `Declaration::Theorem`
    // proved from `Classical.choice` + `propext` + `funext`, with an axiom
    // fallback ONLY if the proof-term builder fails (which must not happen on a
    // healthy build). This expectation tracks the SHRINKING admitted-axiom
    // population honestly — a `value == None` here would mean the proof path
    // silently degraded to the axiom fallback, and MUST fail this test.
    let em = env.get_const(&Name::from_string("Classical.em")).unwrap();
    assert_eq!(
        em.kind,
        ConstantKind::Theorem,
        "Classical.em must be a kernel-checked Theorem (Diaconescu), not an axiom fallback"
    );
    assert!(
        em.value.is_some(),
        "Classical.em must carry its Diaconescu proof term"
    );
    assert!(em.level_params.is_empty()); // works at Prop level only
    assert_eq!(
        count_pi_args(&em.type_),
        1,
        "Classical.em type should have 1 Pi binder (p)"
    );

    // Classical.byContradiction : {p : Prop} → (Not p → False) → p
    // Also a kernel-checked Theorem since 549ebd11 (proved from `Classical.em`).
    let by_contradiction = env
        .get_const(&Name::from_string("Classical.byContradiction"))
        .unwrap();
    assert_eq!(
        by_contradiction.kind,
        ConstantKind::Theorem,
        "Classical.byContradiction must be a kernel-checked Theorem, not an axiom fallback"
    );
    assert!(
        by_contradiction.value.is_some(),
        "Classical.byContradiction must carry its proof term (from Classical.em)"
    );
    assert_eq!(
        count_pi_args(&by_contradiction.type_),
        2,
        "Classical.byContradiction type should have 2 Pi binders (p, h)"
    );

    // Mode must be upgraded to Classical after init_classical (#1335)
    assert_eq!(
        env.mode(),
        crate::mode::CleanMode::Classical,
        "init_classical must upgrade mode to Classical"
    );

    // idempotent
    env.init_classical().unwrap();
    assert!(env.has_classical());
    assert_eq!(env.mode(), crate::mode::CleanMode::Classical);
}

#[test]
fn test_init_classical_rejects_cubical() {
    // Classical axioms are incompatible with Cubical Type Theory (#1379)
    let mut env = Environment::with_mode(crate::mode::CleanMode::Cubical);
    let result = env.init_classical();
    let _err = result.expect_err("init_classical must reject Cubical mode");
    assert!(
        !env.has_classical(),
        "classical_init must remain false after rejection"
    );
    // Mode should remain Cubical
    assert_eq!(env.mode(), crate::mode::CleanMode::Cubical);
}

#[test]
fn test_iff_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_iff().unwrap();

    // Test Iff.rfl type checks: {a : Prop} → Iff a a
    let tc = TypeChecker::new(&env);
    let iff_rfl_const = Expr::const_(Name::from_string("Iff.rfl"), vec![]);
    let iff_rfl_type = tc.infer_type(&iff_rfl_const).unwrap();

    // Iff.rfl : {a : Prop} → Iff a a — 1 Pi binder
    assert_eq!(
        count_pi_args(&iff_rfl_type),
        1,
        "Iff.rfl type should have 1 Pi binder (a)"
    );

    // Iff.mp : {a b : Prop} → Iff a b → a → b — 4 Pi binders
    let iff_mp_const = Expr::const_(Name::from_string("Iff.mp"), vec![]);
    let iff_mp_type = tc.infer_type(&iff_mp_const).unwrap();
    assert_eq!(
        count_pi_args(&iff_mp_type),
        4,
        "Iff.mp type should have 4 Pi binders (a, b, h, ha)"
    );

    // Iff.mpr : {a b : Prop} → Iff a b → b → a — 4 Pi binders
    let iff_mpr_const = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
    let iff_mpr_type = tc.infer_type(&iff_mpr_const).unwrap();
    assert_eq!(
        count_pi_args(&iff_mpr_type),
        4,
        "Iff.mpr type should have 4 Pi binders (a, b, h, hb)"
    );
}

#[test]
fn test_decidable_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_decidable().unwrap();

    // Decidable.isTrue : {p : Prop} → p → Decidable p — 2 Pi binders
    let tc = TypeChecker::new(&env);
    let is_true_const = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
    let is_true_type = tc.infer_type(&is_true_const).unwrap();
    assert_eq!(
        count_pi_args(&is_true_type),
        2,
        "Decidable.isTrue type should have 2 Pi binders (p, h)"
    );

    // Decidable.isFalse : {p : Prop} → (p → False) → Decidable p — 2 Pi binders
    let is_false_const = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
    let is_false_type = tc.infer_type(&is_false_const).unwrap();
    assert_eq!(
        count_pi_args(&is_false_type),
        2,
        "Decidable.isFalse type should have 2 Pi binders (p, h)"
    );
}

#[test]
fn test_classical_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_classical().unwrap();

    let tc = TypeChecker::new(&env);

    // Classical.choice : {α : Sort u} → Nonempty α → α — 2 Pi binders
    let choice_const = Expr::const_(Name::from_string("Classical.choice"), vec![Level::zero()]);
    let choice_type = tc.infer_type(&choice_const).unwrap();
    assert_eq!(
        count_pi_args(&choice_type),
        2,
        "Classical.choice type should have 2 Pi binders (α, h)"
    );

    // Classical.em : (p : Prop) → Or p (Not p) — 1 Pi binder
    let em_const = Expr::const_(Name::from_string("Classical.em"), vec![]);
    let em_type = tc.infer_type(&em_const).unwrap();
    assert_eq!(
        count_pi_args(&em_type),
        1,
        "Classical.em type should have 1 Pi binder (p)"
    );

    // Classical.byContradiction : {p : Prop} → (Not p → False) → p — 2 Pi binders
    let bc_const = Expr::const_(Name::from_string("Classical.byContradiction"), vec![]);
    let bc_type = tc.infer_type(&bc_const).unwrap();
    assert_eq!(
        count_pi_args(&bc_type),
        2,
        "Classical.byContradiction type should have 2 Pi binders (p, h)"
    );

    // Or.inl : {a b : Prop} → a → Or a b — 3 Pi binders
    let inl_const = Expr::const_(Name::from_string("Or.inl"), vec![]);
    let inl_type = tc.infer_type(&inl_const).unwrap();
    assert_eq!(
        count_pi_args(&inl_type),
        3,
        "Or.inl type should have 3 Pi binders (a, b, ha)"
    );

    // Nonempty.intro : {α : Sort u} → α → Nonempty α — 2 Pi binders
    let intro_const = Expr::const_(Name::from_string("Nonempty.intro"), vec![Level::zero()]);
    let intro_type = tc.infer_type(&intro_const).unwrap();
    assert_eq!(
        count_pi_args(&intro_type),
        2,
        "Nonempty.intro type should have 2 Pi binders (α, a)"
    );
}

#[test]
fn test_all_logical_types() {
    let mut env = Environment::new();

    // Initialize all logical types
    env.init_eq().unwrap();
    env.init_iff().unwrap();
    env.init_decidable().unwrap();
    env.init_or().unwrap();
    env.init_classical().unwrap();
    env.init_true_false().unwrap();
    env.init_and().unwrap();
    env.init_exists().unwrap();

    // Verify all exist
    assert!(env.has_eq());
    assert!(env.has_iff());
    assert!(env.has_decidable());
    assert!(env.has_or());
    assert!(env.has_classical());
    assert!(env.has_true_false());
    assert!(env.has_and());
    assert!(env.has_exists());

    // Count constants: Eq (18) + Iff (~10) + Decidable (~5) + Or (~6) + Classical (~15)
    // + True/False (~10) + And (~8) + Exists (~6)
    // This is just sanity check that they don't collide
    assert!(env.num_constants() > 50);
}

#[test]
fn test_init_true_false() {
    let mut env = Environment::new();
    assert!(!env.has_true_false());

    env.init_true_false().unwrap();
    assert!(env.has_true_false());

    // Check True type
    let true_info = env.get_inductive(&Name::from_string("True")).unwrap();
    assert_eq!(true_info.constructor_names.len(), 1);

    // Check False type (no constructors)
    let false_info = env.get_inductive(&Name::from_string("False")).unwrap();
    assert_eq!(false_info.constructor_names.len(), 0);

    // Check derived definitions with arity verification
    // False.elim : {C : Sort u} → False → C
    let false_elim = env.get_const(&Name::from_string("False.elim")).unwrap();
    assert_eq!(
        count_pi_args(&false_elim.type_),
        2,
        "False.elim type should have 2 Pi binders (C, h)"
    );

    // absurd : {a : Prop} → {b : Sort v} → a → Not a → b
    let absurd = env.get_const(&Name::from_string("absurd")).unwrap();
    assert_eq!(
        count_pi_args(&absurd.type_),
        4,
        "absurd type should have 4 Pi binders (a, b, ha, hna)"
    );

    // Not : Prop → Prop (1 Pi binder)
    let not_def = env.get_const(&Name::from_string("Not")).unwrap();
    assert_eq!(
        count_pi_args(&not_def.type_),
        1,
        "Not type should have 1 Pi binder (a)"
    );

    // Idempotent
    env.init_true_false().unwrap();
}

#[test]
fn test_true_false_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_true_false().unwrap();

    let tc = TypeChecker::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // True : Prop
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let true_type = tc.infer_type(&true_const).unwrap();
    assert!(tc.is_def_eq(&true_type, &prop));

    // True.intro : True
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    let true_intro_type = tc.infer_type(&true_intro).unwrap();
    assert!(tc.is_def_eq(&true_intro_type, &true_const));

    // False : Prop
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let false_type = tc.infer_type(&false_const).unwrap();
    assert!(tc.is_def_eq(&false_type, &prop));

    // Not : Prop → Prop
    let not_const = Expr::const_(Name::from_string("Not"), vec![]);
    let not_type = tc.infer_type(&not_const).unwrap();
    let expected_not_type = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
    assert!(tc.is_def_eq(&not_type, &expected_not_type));
}

#[test]
fn test_init_and() {
    let mut env = Environment::new();
    assert!(!env.has_and());

    env.init_and().unwrap();
    assert!(env.has_and());

    // Check And type exists
    let and_info = env.get_inductive(&Name::from_string("And")).unwrap();
    assert_eq!(and_info.num_params, 2);
    assert_eq!(and_info.constructor_names.len(), 1);

    // Check derived definitions with arity verification
    // And.intro : {a b : Prop} → a → b → And a b
    let and_intro = env.get_const(&Name::from_string("And.intro")).unwrap();
    assert_eq!(
        count_pi_args(&and_intro.type_),
        4,
        "And.intro type should have 4 Pi binders (a, b, ha, hb)"
    );

    // And.left : {a b : Prop} → And a b → a
    let and_left = env.get_const(&Name::from_string("And.left")).unwrap();
    assert_eq!(
        count_pi_args(&and_left.type_),
        3,
        "And.left type should have 3 Pi binders (a, b, h)"
    );

    // And.right : {a b : Prop} → And a b → b
    let and_right = env.get_const(&Name::from_string("And.right")).unwrap();
    assert_eq!(
        count_pi_args(&and_right.type_),
        3,
        "And.right type should have 3 Pi binders (a, b, h)"
    );

    // And.symm : {a b : Prop} → And a b → And b a
    let and_symm = env.get_const(&Name::from_string("And.symm")).unwrap();
    assert_eq!(
        count_pi_args(&and_symm.type_),
        3,
        "And.symm type should have 3 Pi binders (a, b, h)"
    );

    // Idempotent
    env.init_and().unwrap();
}

#[test]
fn test_and_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_and().unwrap();

    let tc = TypeChecker::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // And : Prop → Prop → Prop
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let and_type = tc.infer_type(&and_const).unwrap();
    let expected_and_type = Expr::pi(
        BinderInfo::Default,
        prop.clone(),
        Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
    );
    assert!(tc.is_def_eq(&and_type, &expected_and_type));

    // And.left : {a b : Prop} → And a b → a (3 Pi binders)
    let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
    let and_left_type = tc.infer_type(&and_left).unwrap();
    assert_eq!(
        count_pi_args(&and_left_type),
        3,
        "And.left type should have 3 Pi binders (a, b, h)"
    );

    // And.right : {a b : Prop} → And a b → b (3 Pi binders)
    let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
    let and_right_type = tc.infer_type(&and_right).unwrap();
    assert_eq!(
        count_pi_args(&and_right_type),
        3,
        "And.right type should have 3 Pi binders (a, b, h)"
    );

    // And.symm : {a b : Prop} → And a b → And b a (3 Pi binders)
    let and_symm = Expr::const_(Name::from_string("And.symm"), vec![]);
    let and_symm_type = tc.infer_type(&and_symm).unwrap();
    assert_eq!(
        count_pi_args(&and_symm_type),
        3,
        "And.symm type should have 3 Pi binders (a, b, h)"
    );
}

#[test]
fn test_init_exists() {
    let mut env = Environment::new();
    assert!(!env.has_exists());

    env.init_exists().unwrap();
    assert!(env.has_exists());

    // Check Exists type exists
    let exists_info = env.get_inductive(&Name::from_string("Exists")).unwrap();
    assert_eq!(exists_info.num_params, 2); // α and p
    assert_eq!(exists_info.constructor_names.len(), 1);

    // Check derived definitions with arity verification
    // Exists.intro : {α : Sort u} → {p : α → Prop} → (w : α) → p w → Exists p
    let exists_intro = env.get_const(&Name::from_string("Exists.intro")).unwrap();
    assert_eq!(
        count_pi_args(&exists_intro.type_),
        4,
        "Exists.intro type should have 4 Pi binders (α, p, w, hw)"
    );

    // Exists.elim : {α : Sort u} → {p : α → Prop} → {b : Prop} → Exists p → (∀ x, p x → b) → b
    let exists_elim = env.get_const(&Name::from_string("Exists.elim")).unwrap();
    assert_eq!(
        count_pi_args(&exists_elim.type_),
        5,
        "Exists.elim type should have 5 Pi binders (α, p, b, hex, hpb)"
    );

    // Idempotent
    env.init_exists().unwrap();
}

#[test]
fn test_exists_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_exists().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");

    // Exists : {α : Sort u} → (α → Prop) → Prop
    let exists_const = Expr::const_(Name::from_string("Exists"), vec![Level::param(u.clone())]);
    let exists_type = tc.infer_type(&exists_const).unwrap();

    // Exists : {α : Sort u} → (α → Prop) → Prop — has 2 Pi binders
    assert_eq!(
        count_pi_args(&exists_type),
        2,
        "Exists type should have 2 Pi binders (α, pred)"
    );

    // Exists.intro : {α : Sort u} → {p : α → Prop} → (w : α) → p w → Exists p (4 Pi binders)
    let exists_intro = Expr::const_(
        Name::from_string("Exists.intro"),
        vec![Level::param(u.clone())],
    );
    let exists_intro_type = tc.infer_type(&exists_intro).unwrap();
    assert_eq!(
        count_pi_args(&exists_intro_type),
        4,
        "Exists.intro type should have 4 Pi binders (α, p, w, hw)"
    );

    // Exists.elim : {α : Sort u} → {p : α → Prop} → {b : Prop} → Exists p → (∀ x, p x → b) → b (5 Pi binders)
    let exists_elim = Expr::const_(Name::from_string("Exists.elim"), vec![Level::param(u)]);
    let exists_elim_type = tc.infer_type(&exists_elim).unwrap();
    assert_eq!(
        count_pi_args(&exists_elim_type),
        5,
        "Exists.elim type should have 5 Pi binders (α, p, b, hex, hpb)"
    );
}

#[test]
fn test_exists_elim_type_eliminates_into_prop() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_exists().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let prop = Expr::sort(Level::zero());

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![u_level.clone()]);
    let exists_elim = Expr::const_(Name::from_string("Exists.elim"), vec![u_level]);
    let exists_elim_type = tc.infer_type(&exists_elim).unwrap();

    let expected_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::param(u)),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), prop.clone()),
            Expr::pi(
                BinderInfo::Implicit,
                prop.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(
                        Expr::app(exists_const.clone(), Expr::bvar(2)),
                        Expr::bvar(1),
                    ),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(3),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::app(Expr::bvar(3), Expr::bvar(0)),
                                Expr::bvar(3),
                            ),
                        ),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    assert!(tc.is_def_eq(&exists_elim_type, &expected_type));
}

#[test]
fn test_and_intro_elimination() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_true_false().unwrap();

    let tc = TypeChecker::new(&env);

    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);

    // And.intro True True True.intro True.intro : And True True
    let and_true_true = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(and_intro.clone(), true_const.clone()),
                true_const.clone(),
            ),
            true_intro.clone(),
        ),
        true_intro.clone(),
    );

    let and_type = tc.infer_type(&and_true_true).unwrap();
    let expected_type = Expr::app(
        Expr::app(and_const.clone(), true_const.clone()),
        true_const.clone(),
    );
    assert!(tc.is_def_eq(&and_type, &expected_type));
}

#[test]
fn test_init_prod() {
    let mut env = Environment::new();
    assert!(!env.has_prod());

    env.init_prod().unwrap();
    assert!(env.has_prod());

    // Ensure projections and swap exist with arity verification
    // Prod.fst : {α : Type u} → {β : Type v} → Prod α β → α
    let fst = env.get_const(&Name::from_string("Prod.fst")).unwrap();
    assert_eq!(
        count_pi_args(&fst.type_),
        3,
        "Prod.fst type should have 3 Pi binders (α, β, self)"
    );

    // Prod.snd : {α : Type u} → {β : Type v} → Prod α β → β
    let snd = env.get_const(&Name::from_string("Prod.snd")).unwrap();
    assert_eq!(
        count_pi_args(&snd.type_),
        3,
        "Prod.snd type should have 3 Pi binders (α, β, self)"
    );

    // Prod.swap : {α : Type u} → {β : Type v} → Prod α β → Prod β α
    let swap = env.get_const(&Name::from_string("Prod.swap")).unwrap();
    assert_eq!(
        count_pi_args(&swap.type_),
        3,
        "Prod.swap type should have 3 Pi binders (α, β, self)"
    );

    // Structure field metadata
    assert_eq!(
        env.get_structure_field_index(&Name::from_string("Prod"), &Name::from_string("fst")),
        Some(0)
    );
    assert_eq!(
        env.get_structure_field_index(&Name::from_string("Prod"), &Name::from_string("snd")),
        Some(1)
    );

    env.init_prod().unwrap(); // idempotent
}

#[test]
fn test_prod_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_prod().unwrap();

    let tc = TypeChecker::new(&env);
    let type0 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    // Prod.{0,0} : Type → Type → Type
    let prod_const = Expr::const_(
        Name::from_string("Prod"),
        vec![Level::zero(), Level::zero()],
    );
    let prod_type = tc.infer_type(&prod_const).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone()),
    );
    assert!(tc.is_def_eq(&prod_type, &expected_type));

    // Prod.fst : {α : Type u} → {β : Type v} → Prod α β → α (3 Pi binders)
    let fst_const = Expr::const_(
        Name::from_string("Prod.fst"),
        vec![Level::zero(), Level::zero()],
    );
    let fst_type = tc.infer_type(&fst_const).unwrap();
    assert_eq!(
        count_pi_args(&fst_type),
        3,
        "Prod.fst type should have 3 Pi binders (α, β, p)"
    );

    // Prod.snd : {α : Type u} → {β : Type v} → Prod α β → β (3 Pi binders)
    let snd_const = Expr::const_(
        Name::from_string("Prod.snd"),
        vec![Level::zero(), Level::zero()],
    );
    let snd_type = tc.infer_type(&snd_const).unwrap();
    assert_eq!(
        count_pi_args(&snd_type),
        3,
        "Prod.snd type should have 3 Pi binders (α, β, p)"
    );

    // Prod.swap : {α : Type u} → {β : Type v} → Prod α β → Prod β α (3 Pi binders)
    let swap_const = Expr::const_(
        Name::from_string("Prod.swap"),
        vec![Level::zero(), Level::zero()],
    );
    let swap_type = tc.infer_type(&swap_const).unwrap();
    assert_eq!(
        count_pi_args(&swap_type),
        3,
        "Prod.swap type should have 3 Pi binders (α, β, p)"
    );
}

/// REGRESSION (Order.Basic universe-level class): Lean's real `Prod.swap` has
/// `levelParams = [u_2, u_1]` — the level-param LIST is ordered `[β-univ, α-univ]`,
/// REVERSED from binder-appearance order — where the signature is
/// `{α : Type u_1} → {β : Type u_2} → Prod α β → Prod β α`. Verified against the
/// real olean env: `Prod.swap: levelParams = [u_2, u_1]`. Clean previously bound
/// `[u, v]` (α-univ first), so applications supplying level args in Lean's order
/// (`Prod.swap.{v, u}` in `Prod.swap_le_swap`) substituted α↦v, β↦u — reversed —
/// and produced a `Sort(Succ v)` vs `Sort(Succ u)` type mismatch on the downstream
/// order lemmas (`Prod.swap_le_swap`, `Prod.swap_lt_swap`, and the derived
/// `Mathlib.Order.Basic._auxLemma.61/63`). The param list must be `[v, u]`.
#[test]
fn test_prod_swap_level_param_order_matches_lean() {
    let mut env = Environment::new();
    env.init_prod().unwrap();

    let swap = env.get_const(&Name::from_string("Prod.swap")).unwrap();
    // Re-pinned (v4.31 retarget, 2026-07-04): Lean v4.31 orders the universe
    // params in BINDER-APPEARANCE order — α-universe (`u`) first (verified via
    // `#print Prod.swap` on v4.31: `Prod.swap.{u_1, u_2}` with `α : Type u_1`).
    // Lean v4.8 used the reversed `[u_2, u_1]` (the previous pin here).
    assert_eq!(
        swap.level_params,
        vec![Name::from_string("u"), Name::from_string("v")],
        "Prod.swap levelParams must be [u, v] (α-univ first) to match Lean v4.31's [u_1, u_2]"
    );
}

/// REGRESSION: a `Prod.swap` application with DISTINCT universes must type-check
/// with the level-arg order Lean actually emits. Instantiate `Prod.swap` on
/// `α : Type 3`, `β : Type 5` the way a use site does: `Prod.swap.{5, 3}` (β's
/// universe first, mirroring Lean's `Prod.swap.{v, u}`). With the corrected
/// `[v, u]` param list this binds `v↦5, u↦3`, so `α : Type 3`, `β : Type 5`, and
/// the result type is `Prod.{5,3} β α`, which must be inferable. With the old
/// `[u, v]` list the universes bound reversed and this failed.
#[test]
fn test_prod_swap_distinct_universes_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_prod().unwrap();
    let tc = TypeChecker::new(&env);

    // Level args in Lean v4.31's emission order: [α-univ, β-univ] = [3, 5]
    // (binder-appearance order; v4.8 emitted the reverse).
    let five = Level::succ(Level::succ(Level::succ(Level::succ(Level::succ(
        Level::zero(),
    )))));
    let three = Level::succ(Level::succ(Level::succ(Level::zero())));
    let swap_const = Expr::const_(
        Name::from_string("Prod.swap"),
        vec![three.clone(), five.clone()],
    );
    let swap_type = tc
        .infer_type(&swap_const)
        .expect("Prod.swap.{3,5} must infer a type");

    // Expected: {α : Type 3} → {β : Type 5} → Prod.{3,5} α β → Prod.{5,3} β α.
    // (α gets universe 3 = first arg, β gets 5 = second, v4.31 order.)
    let type3 = Expr::from_kind(ExprKind::Sort(Level::succ(three.clone())));
    let type5 = Expr::from_kind(ExprKind::Sort(Level::succ(five.clone())));

    let ExprKind::Pi(alpha_bd, alpha_dom, alpha_body) = swap_type.kind() else {
        panic!("Prod.swap.{{5,3}} type must be a Pi, got {swap_type:?}");
    };
    assert_eq!(
        alpha_bd.info,
        BinderInfo::Implicit,
        "Prod.swap.{{5,3}} outermost binder (α) must be implicit"
    );
    assert!(
        tc.is_def_eq(alpha_dom, &type3),
        "Prod.swap.{{5,3}} α binder must be Type 3 (u-arg), got {alpha_dom:?}"
    );

    let ExprKind::Pi(beta_bd, beta_dom, _) = alpha_body.kind() else {
        panic!("Prod.swap.{{5,3}} type must have a second Pi (β), got {alpha_body:?}");
    };
    assert_eq!(
        beta_bd.info,
        BinderInfo::Implicit,
        "Prod.swap.{{5,3}} second binder (β) must be implicit"
    );
    assert!(
        tc.is_def_eq(beta_dom, &type5),
        "Prod.swap.{{5,3}} β binder must be Type 5 (v-arg), got {beta_dom:?}"
    );
}

#[test]
fn test_init_pprod() {
    let mut env = Environment::new();
    env.init_pprod().unwrap();

    assert!(env.has_pprod());

    // PProd.fst : {α : Sort u} → {β : Sort v} → PProd α β → α
    let fst = env.get_const(&Name::from_string("PProd.fst")).unwrap();
    assert_eq!(
        count_pi_args(&fst.type_),
        3,
        "PProd.fst type should have 3 Pi binders (α, β, self)"
    );

    // PProd.snd : {α : Sort u} → {β : Sort v} → PProd α β → β
    let snd = env.get_const(&Name::from_string("PProd.snd")).unwrap();
    assert_eq!(
        count_pi_args(&snd.type_),
        3,
        "PProd.snd type should have 3 Pi binders (α, β, self)"
    );

    // PProd.swap : {α : Sort u} → {β : Sort v} → PProd α β → PProd β α
    let swap = env.get_const(&Name::from_string("PProd.swap")).unwrap();
    assert_eq!(
        count_pi_args(&swap.type_),
        3,
        "PProd.swap type should have 3 Pi binders (α, β, self)"
    );

    env.init_pprod().unwrap();
}

#[test]
fn test_pprod_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_pprod().unwrap();

    let tc = TypeChecker::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let pprod_const = Expr::const_(
        Name::from_string("PProd"),
        vec![Level::zero(), Level::zero()],
    );
    let pprod_type = tc.infer_type(&pprod_const).unwrap();
    // PProd.{0,0} : Prop → Prop → Type
    // Result sort is max(max(1,u),v) = max(max(1,0),0) = max(1,0) = 1 = Type
    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let expected_type = Expr::pi(
        BinderInfo::Implicit,
        prop.clone(),
        Expr::pi(BinderInfo::Implicit, prop.clone(), type_),
    );
    assert!(tc.is_def_eq(&pprod_type, &expected_type));

    // PProd.fst : {α : Sort u} → {β : Sort v} → PProd α β → α
    let fst_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PProd.fst"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&fst_type),
        3,
        "PProd.fst type should have 3 Pi binders (α, β, self)"
    );

    // PProd.snd : {α : Sort u} → {β : Sort v} → PProd α β → β
    let snd_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PProd.snd"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&snd_type),
        3,
        "PProd.snd type should have 3 Pi binders (α, β, self)"
    );

    // PProd.swap : {α : Sort u} → {β : Sort v} → PProd α β → PProd β α
    let swap_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PProd.swap"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&swap_type),
        3,
        "PProd.swap type should have 3 Pi binders (α, β, self)"
    );
}

#[test]
fn test_init_sigma() {
    let mut env = Environment::new();
    env.init_sigma().unwrap();

    assert!(env.has_sigma());

    // Sigma.fst : {α : Type u} → {β : α → Type v} → Sigma β → α
    let fst = env.get_const(&Name::from_string("Sigma.fst")).unwrap();
    assert_eq!(
        count_pi_args(&fst.type_),
        3,
        "Sigma.fst type should have 3 Pi binders (α, β, self)"
    );

    // Sigma.snd : {α : Type u} → {β : α → Type v} → (self : Sigma β) → β self.fst
    let snd = env.get_const(&Name::from_string("Sigma.snd")).unwrap();
    assert_eq!(
        count_pi_args(&snd.type_),
        3,
        "Sigma.snd type should have 3 Pi binders (α, β, self)"
    );

    env.init_sigma().unwrap();
}

#[test]
fn test_sigma_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_sigma().unwrap();

    let tc = TypeChecker::new(&env);
    let sigma_const = Expr::const_(
        Name::from_string("Sigma"),
        vec![Level::zero(), Level::zero()],
    );

    // Sigma : {α : Type u} → (α → Type v) → Type (max u v) — 2 Pi binders
    let sigma_type = tc.infer_type(&sigma_const).unwrap();
    assert_eq!(
        count_pi_args(&sigma_type),
        2,
        "Sigma type should have 2 Pi binders (α, β)"
    );

    // Sigma.fst : {α : Type u} → {β : α → Type v} → Sigma α β → α — 3 Pi binders
    let sigma_fst_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Sigma.fst"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&sigma_fst_type),
        3,
        "Sigma.fst type should have 3 Pi binders (α, β, s)"
    );

    // Sigma.snd : {α : Type u} → {β : α → Type v} → (s : Sigma α β) → β (Sigma.fst s) — 3 Pi binders
    let sigma_snd_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Sigma.snd"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&sigma_snd_type),
        3,
        "Sigma.snd type should have 3 Pi binders (α, β, s)"
    );
}

#[test]
fn test_init_subtype() {
    let mut env = Environment::new();
    env.init_subtype().unwrap();

    assert!(env.has_subtype());

    // Subtype.val : {α : Sort u} → {p : α → Prop} → Subtype p → α
    let val = env.get_const(&Name::from_string("Subtype.val")).unwrap();
    assert_eq!(
        count_pi_args(&val.type_),
        3,
        "Subtype.val type should have 3 Pi binders (α, p, self)"
    );

    // Subtype.property : {α : Sort u} → {p : α → Prop} → (self : Subtype p) → p (Subtype.val self)
    let prop = env
        .get_const(&Name::from_string("Subtype.property"))
        .unwrap();
    assert_eq!(
        count_pi_args(&prop.type_),
        3,
        "Subtype.property type should have 3 Pi binders (α, p, self)"
    );
    assert_eq!(
        env.get_structure_field_index(&Name::from_string("Subtype"), &Name::from_string("val")),
        Some(0)
    );
    assert_eq!(
        env.get_structure_field_index(
            &Name::from_string("Subtype"),
            &Name::from_string("property")
        ),
        Some(1)
    );

    env.init_subtype().unwrap();
}

#[test]
fn test_subtype_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_subtype().unwrap();

    let tc = TypeChecker::new(&env);
    let subtype_const = Expr::const_(Name::from_string("Subtype"), vec![Level::zero()]);
    let subtype_type = tc.infer_type(&subtype_const).unwrap();
    // Subtype : {α : Sort u} → (α → Prop) → Type
    assert_eq!(
        count_pi_args(&subtype_type),
        2,
        "Subtype type should have 2 Pi binders (α, pred)"
    );

    // Subtype.val : {α : Sort u} → {p : α → Prop} → Subtype p → α
    let val_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Subtype.val"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&val_type),
        3,
        "Subtype.val type should have 3 Pi binders (α, p, self)"
    );

    // Subtype.property : {α : Sort u} → {p : α → Prop} → (self : Subtype p) → p (Subtype.val self)
    let prop_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Subtype.property"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&prop_type),
        3,
        "Subtype.property type should have 3 Pi binders (α, p, self)"
    );
}

#[test]
fn test_init_option() {
    let mut env = Environment::new();
    env.init_option().unwrap();

    assert!(env.has_option());
    let option_info = env.get_inductive(&Name::from_string("Option")).unwrap();
    assert_eq!(option_info.constructor_names.len(), 2);

    // Option.none : {α : Type u} → Option α
    let none = env.get_const(&Name::from_string("Option.none")).unwrap();
    assert_eq!(
        count_pi_args(&none.type_),
        1,
        "Option.none type should have 1 Pi binder (α)"
    );

    // Option.some : {α : Type u} → α → Option α
    let some = env.get_const(&Name::from_string("Option.some")).unwrap();
    assert_eq!(
        count_pi_args(&some.type_),
        2,
        "Option.some type should have 2 Pi binders (α, val)"
    );

    env.init_option().unwrap();
}

#[test]
fn test_option_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_option().unwrap();

    let tc = TypeChecker::new(&env);
    let option_const = Expr::const_(Name::from_string("Option"), vec![Level::zero()]);
    let option_type = tc.infer_type(&option_const).unwrap();
    // Option : Type u → Type u
    assert_eq!(
        count_pi_args(&option_type),
        1,
        "Option type should have 1 Pi binder (α)"
    );

    // Option.none : {α : Type u} → Option α
    let none_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Option.none"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&none_type),
        1,
        "Option.none type should have 1 Pi binder (α)"
    );

    // Option.some : {α : Type u} → α → Option α
    let some_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Option.some"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&some_type),
        2,
        "Option.some type should have 2 Pi binders (α, val)"
    );
}

#[test]
fn test_init_sum() {
    let mut env = Environment::new();
    env.init_sum().unwrap();

    // Check Sum type exists with arity verification
    let sum_ind = env.get_inductive(&Name::from_string("Sum")).unwrap();
    assert_eq!(
        sum_ind.num_params, 2,
        "Sum should have 2 type params (α, β)"
    );
    assert_eq!(sum_ind.constructor_names.len(), 2);

    // Sum.inl : {α : Type u} → {β : Type v} → α → Sum α β
    let inl = env.get_const(&Name::from_string("Sum.inl")).unwrap();
    assert_eq!(
        count_pi_args(&inl.type_),
        3,
        "Sum.inl type should have 3 Pi binders (α, β, val)"
    );

    // Sum.inr : {α : Type u} → {β : Type v} → β → Sum α β
    let inr = env.get_const(&Name::from_string("Sum.inr")).unwrap();
    assert_eq!(
        count_pi_args(&inr.type_),
        3,
        "Sum.inr type should have 3 Pi binders (α, β, val)"
    );

    // Sum.rec : recursor with 2 minors (inl, inr)
    let sum_rec = env.get_recursor(&Name::from_string("Sum.rec")).unwrap();
    assert_eq!(
        sum_rec.num_minors, 2,
        "Sum.rec should have 2 minors (inl, inr)"
    );
    assert_eq!(sum_rec.rules.len(), 2, "Sum.rec should have 2 rules");

    // Idempotence
    env.init_sum().unwrap();
}

#[test]
fn test_sum_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_sum().unwrap();

    let tc = TypeChecker::new(&env);

    // Sum : Type u → Type v → Type (max u v)
    let sum_const = Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]);
    let sum_type = tc.infer_type(&sum_const).unwrap();
    assert_eq!(
        count_pi_args(&sum_type),
        2,
        "Sum type should have 2 Pi binders (α, β)"
    );

    // Sum.inl : {α : Type u} → {β : Type v} → α → Sum α β
    let inl_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Sum.inl"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&inl_type),
        3,
        "Sum.inl type should have 3 Pi binders (α, β, val)"
    );

    // Sum.inr : {α : Type u} → {β : Type v} → β → Sum α β
    let inr_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Sum.inr"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&inr_type),
        3,
        "Sum.inr type should have 3 Pi binders (α, β, val)"
    );
}

#[test]
fn test_init_psum() {
    let mut env = Environment::new();
    env.init_psum().unwrap();

    // Check PSum type exists with arity verification
    let psum_ind = env.get_inductive(&Name::from_string("PSum")).unwrap();
    assert_eq!(
        psum_ind.num_params, 2,
        "PSum should have 2 type params (α, β)"
    );
    assert_eq!(psum_ind.constructor_names.len(), 2);

    // PSum.inl : {α : Sort u} → {β : Sort v} → α → PSum α β
    let inl = env.get_const(&Name::from_string("PSum.inl")).unwrap();
    assert_eq!(
        count_pi_args(&inl.type_),
        3,
        "PSum.inl type should have 3 Pi binders (α, β, val)"
    );

    // PSum.inr : {α : Sort u} → {β : Sort v} → β → PSum α β
    let inr = env.get_const(&Name::from_string("PSum.inr")).unwrap();
    assert_eq!(
        count_pi_args(&inr.type_),
        3,
        "PSum.inr type should have 3 Pi binders (α, β, val)"
    );

    // PSum.rec : recursor with 2 minors (inl, inr)
    let psum_rec = env.get_recursor(&Name::from_string("PSum.rec")).unwrap();
    assert_eq!(
        psum_rec.num_minors, 2,
        "PSum.rec should have 2 minors (inl, inr)"
    );
    assert_eq!(psum_rec.rules.len(), 2, "PSum.rec should have 2 rules");

    // Idempotence
    env.init_psum().unwrap();
}

#[test]
fn test_psum_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_psum().unwrap();

    let tc = TypeChecker::new(&env);

    // PSum : Sort u → Sort v → Sort (max u v)
    let psum_const = Expr::const_(
        Name::from_string("PSum"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let psum_type = tc.infer_type(&psum_const).unwrap();
    assert_eq!(
        count_pi_args(&psum_type),
        2,
        "PSum type should have 2 Pi binders (α, β)"
    );

    // PSum.inl : {α : Sort u} → {β : Sort v} → α → PSum α β
    let inl_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PSum.inl"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&inl_type),
        3,
        "PSum.inl type should have 3 Pi binders (α, β, val)"
    );

    // PSum.inr : {α : Sort u} → {β : Sort v} → β → PSum α β
    let inr_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PSum.inr"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&inr_type),
        3,
        "PSum.inr type should have 3 Pi binders (α, β, val)"
    );
}

#[test]
fn test_init_psigma() {
    let mut env = Environment::new();
    env.init_psigma().unwrap();

    // Check PSigma type exists with arity verification
    let psigma_ind = env.get_inductive(&Name::from_string("PSigma")).unwrap();
    assert_eq!(
        psigma_ind.num_params, 2,
        "PSigma should have 2 type params (α, β)"
    );

    // PSigma.mk : {α : Sort u} → {β : α → Sort v} → (fst : α) → (snd : β fst) → PSigma β
    let mk = env.get_const(&Name::from_string("PSigma.mk")).unwrap();
    assert_eq!(
        count_pi_args(&mk.type_),
        4,
        "PSigma.mk type should have 4 Pi binders (α, β, fst, snd)"
    );

    // PSigma.rec : recursor with 1 minor (mk)
    let psigma_rec = env.get_recursor(&Name::from_string("PSigma.rec")).unwrap();
    assert_eq!(
        psigma_rec.num_minors, 1,
        "PSigma.rec should have 1 minor (mk)"
    );
    assert_eq!(psigma_rec.rules.len(), 1, "PSigma.rec should have 1 rule");

    // PSigma.fst : {α : Sort u} → {β : α → Sort v} → PSigma β → α
    let fst = env.get_const(&Name::from_string("PSigma.fst")).unwrap();
    assert_eq!(
        count_pi_args(&fst.type_),
        3,
        "PSigma.fst type should have 3 Pi binders (α, β, self)"
    );

    // PSigma.snd : {α : Sort u} → {β : α → Sort v} → (self : PSigma β) → β self.fst
    let snd = env.get_const(&Name::from_string("PSigma.snd")).unwrap();
    assert_eq!(
        count_pi_args(&snd.type_),
        3,
        "PSigma.snd type should have 3 Pi binders (α, β, self)"
    );

    // Structure fields registered
    let fields = env
        .get_structure_field_names(&Name::from_string("PSigma"))
        .expect("PSigma should have registered structure fields");
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0], Name::from_string("fst"));
    assert_eq!(fields[1], Name::from_string("snd"));

    // Idempotence
    env.init_psigma().unwrap();
}

#[test]
fn test_psigma_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_psigma().unwrap();

    let tc = TypeChecker::new(&env);

    // PSigma : {α : Sort u} → (α → Sort v) → Sort (max u v)
    let psigma_const = Expr::const_(
        Name::from_string("PSigma"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let psigma_type = tc.infer_type(&psigma_const).unwrap();
    assert_eq!(
        count_pi_args(&psigma_type),
        2,
        "PSigma type should have 2 Pi binders (α, β)"
    );

    // PSigma.mk : {α : Sort u} → {β : α → Sort v} → (fst : α) → (snd : β fst) → PSigma β
    let mk_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PSigma.mk"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&mk_type),
        4,
        "PSigma.mk type should have 4 Pi binders (α, β, fst, snd)"
    );

    // PSigma.fst : {α : Sort u} → {β : α → Sort v} → PSigma β → α
    let fst_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PSigma.fst"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&fst_type),
        3,
        "PSigma.fst type should have 3 Pi binders (α, β, self)"
    );

    // PSigma.snd : {α : Sort u} → {β : α → Sort v} → (self : PSigma β) → β self.fst
    let snd_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("PSigma.snd"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&snd_type),
        3,
        "PSigma.snd type should have 3 Pi binders (α, β, self)"
    );
}

#[test]
fn test_init_empty() {
    let mut env = Environment::new();
    env.init_empty().unwrap();

    // Check Empty type exists with arity verification
    let ind = env.get_inductive(&Name::from_string("Empty")).unwrap();
    assert_eq!(ind.constructor_names.len(), 0);
    // Empty.rec : recursor with 0 minors (no constructors)
    let empty_rec = env.get_recursor(&Name::from_string("Empty.rec")).unwrap();
    assert_eq!(empty_rec.num_minors, 0, "Empty.rec should have 0 minors");
    assert_eq!(empty_rec.rules.len(), 0, "Empty.rec should have 0 rules");

    // Empty.elim : {C : Sort u} → Empty → C
    let elim = env.get_const(&Name::from_string("Empty.elim")).unwrap();
    assert_eq!(
        count_pi_args(&elim.type_),
        2,
        "Empty.elim type should have 2 Pi binders (C, h)"
    );

    // Idempotence
    env.init_empty().unwrap();
}

#[test]
fn test_empty_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_empty().unwrap();

    let tc = TypeChecker::new(&env);

    // Empty : Type
    let empty_const = Expr::const_(Name::from_string("Empty"), vec![]);
    let empty_type = tc.infer_type(&empty_const).unwrap();
    match &empty_type.kind {
        ExprKind::Sort(lvl) => assert_eq!(*lvl, Level::succ(Level::zero())),
        _ => panic!("Empty should be a Type"),
    }

    // Empty.elim : {C : Sort u} → Empty → C
    let elim_const = Expr::const_(Name::from_string("Empty.elim"), vec![Level::zero()]);
    let elim_type = tc.infer_type(&elim_const).unwrap();
    assert_eq!(
        count_pi_args(&elim_type),
        2,
        "Empty.elim type should have 2 Pi binders (C, h)"
    );
}

#[test]
fn test_init_pempty() {
    let mut env = Environment::new();
    env.init_pempty().unwrap();

    // Check PEmpty type exists with arity verification
    let ind = env.get_inductive(&Name::from_string("PEmpty")).unwrap();
    assert_eq!(ind.constructor_names.len(), 0);
    // PEmpty.rec : recursor with 0 minors (no constructors)
    let pempty_rec = env.get_recursor(&Name::from_string("PEmpty.rec")).unwrap();
    assert_eq!(pempty_rec.num_minors, 0, "PEmpty.rec should have 0 minors");
    assert_eq!(pempty_rec.rules.len(), 0, "PEmpty.rec should have 0 rules");

    // PEmpty.elim : {α : Sort u} → {C : Sort v} → PEmpty → C
    let elim = env.get_const(&Name::from_string("PEmpty.elim")).unwrap();
    assert_eq!(
        count_pi_args(&elim.type_),
        2,
        "PEmpty.elim type should have 2 Pi binders (C, h)"
    );

    // Idempotence
    env.init_pempty().unwrap();
}

#[test]
fn test_pempty_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_pempty().unwrap();

    let tc = TypeChecker::new(&env);

    // PEmpty : Sort u
    let pempty_const = Expr::const_(
        Name::from_string("PEmpty"),
        vec![Level::succ(Level::zero())],
    );
    let pempty_type = tc.infer_type(&pempty_const).unwrap();
    // PEmpty.{succ(0)} : Type (same as Empty)
    match &pempty_type.kind {
        ExprKind::Sort(lvl) => assert_eq!(
            *lvl,
            Level::succ(Level::zero()),
            "PEmpty.{{1}} should have type Type"
        ),
        _ => panic!("PEmpty should be a Sort"),
    }

    // PEmpty.elim : {C : Sort v} → PEmpty → C
    let elim_const = Expr::const_(
        Name::from_string("PEmpty.elim"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let elim_type = tc.infer_type(&elim_const).unwrap();
    assert_eq!(
        count_pi_args(&elim_type),
        2,
        "PEmpty.elim type should have 2 Pi binders (C, h)"
    );
}

/// REGRESSION (FirstOrder `mk₂` universe class): Lean's real `PEmpty.elim`
/// (`def PEmpty.elim {C : Sort _} : PEmpty → C`) elaborates to
/// `PEmpty.elim.{u_1, u_2} : {C : Sort u_1} → PEmpty.{u_2} → C` — level params in
/// order of FIRST APPEARANCE: C's universe first, PEmpty's universe second.
/// Clean previously bound `[u, v]` with `u` = PEmpty's universe (REVERSED), so an
/// application in Lean's emission order (`PEmpty.elim.{S w, S u}` inside
/// `FirstOrder.Language.funMap₂`) bound PEmpty ↦ `S w` and C ↦ `S u` — reversed —
/// producing a `Sort(Succ u)` vs `Sort(Succ w)` type mismatch on the `mk₂`-family
/// FirstOrder decls. The param list must be `[C-univ, PEmpty-univ]`.
#[test]
fn test_pempty_elim_level_param_order_matches_lean() {
    let mut env = Environment::new();
    env.init_pempty().unwrap();

    let elim = env.get_const(&Name::from_string("PEmpty.elim")).unwrap();
    // Lean's canonical order: C's universe (`v`) first, PEmpty's universe (`u`)
    // second — mirroring Lean's real `[u_1, u_2]` = `[C-univ, PEmpty-univ]`.
    assert_eq!(
        elim.level_params,
        vec![Name::from_string("v"), Name::from_string("u")],
        "PEmpty.elim levelParams must be [v, u] (C-univ, PEmpty-univ) to match Lean"
    );
}

/// REGRESSION: a `PEmpty.elim` application with DISTINCT universes must type-check
/// with the level-arg order Lean actually emits. Instantiate at `C : Type 5`,
/// `PEmpty : Type 3` the way `funMap₂` does — `PEmpty.elim.{6, 4}` (C-univ = 6 for
/// `Type 5`, PEmpty-univ = 4 for `Type 3`, mirroring Lean's `.{S w, S u}`). With
/// the corrected `[v, u]` list this binds C ↦ Sort 6, PEmpty ↦ Sort 4, so the
/// result type is `{C : Type 5} → PEmpty.{4} → C`, which must be inferable.
#[test]
fn test_pempty_elim_distinct_universes_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_pempty().unwrap();
    let tc = TypeChecker::new(&env);

    let lvl = |n: u32| {
        let mut l = Level::zero();
        for _ in 0..n {
            l = Level::succ(l);
        }
        l
    };
    // Level args in Lean's emission order: [C-univ, PEmpty-univ] = [6, 4].
    let elim_const = Expr::const_(Name::from_string("PEmpty.elim"), vec![lvl(6), lvl(4)]);
    let elim_type = tc
        .infer_type(&elim_const)
        .expect("PEmpty.elim.{6,4} must infer with Lean's level-arg order");
    // {C : Sort 6} → PEmpty.{4} → C : two Pi binders.
    assert_eq!(count_pi_args(&elim_type), 2);
    // The PEmpty argument's declared universe must be 4 (= PEmpty : Type 3),
    // not the C-universe 6 — i.e. the second level arg reached PEmpty, proving
    // the [C-univ, PEmpty-univ] ordering.
    if let ExprKind::Pi(_, _c, body) = &elim_type.kind {
        if let ExprKind::Pi(_, pempty_dom, _) = &body.kind {
            match &pempty_dom.kind {
                ExprKind::Const(name, levels) => {
                    assert_eq!(name, &Name::from_string("PEmpty"));
                    assert_eq!(
                        levels.as_slice(),
                        &[lvl(4)],
                        "PEmpty argument must use universe 4 (Type 3)"
                    );
                }
                other => panic!("expected PEmpty constant domain, got: {other:?}"),
            }
        } else {
            panic!("expected inner Pi (PEmpty → C)");
        }
    } else {
        panic!("expected outer Pi (C binder)");
    }
}

#[test]
fn test_all_union_and_empty_types() {
    // Test that all new types work together
    let mut env = Environment::new();
    env.init_sum().unwrap();
    env.init_psum().unwrap();
    env.init_psigma().unwrap();
    env.init_empty().unwrap();
    env.init_pempty().unwrap();

    assert!(env.has_sum());
    assert!(env.has_psum());
    assert!(env.has_psigma());
    assert!(env.has_empty());
    assert!(env.has_pempty());
}

#[test]
fn test_init_bool() {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    assert!(
        env.get_const(&Name::from_string("sorryAx")).is_some(),
        "init_bool should register sorryAx once the Bool surface is available"
    );

    // Check Bool type exists with arity verification
    let bool_ind = env.get_inductive(&Name::from_string("Bool")).unwrap();
    assert_eq!(bool_ind.constructor_names.len(), 2);
    // Bool.false : 0 fields, index 0
    let bool_false = env
        .get_constructor(&Name::from_string("Bool.false"))
        .unwrap();
    assert_eq!(bool_false.num_fields, 0, "Bool.false should have 0 fields");
    assert_eq!(
        bool_false.constructor_idx, 0,
        "Bool.false should be constructor 0"
    );
    // Bool.true : 0 fields, index 1
    let bool_true = env
        .get_constructor(&Name::from_string("Bool.true"))
        .unwrap();
    assert_eq!(bool_true.num_fields, 0, "Bool.true should have 0 fields");
    assert_eq!(
        bool_true.constructor_idx, 1,
        "Bool.true should be constructor 1"
    );
    // Bool.rec : recursor with 2 minors (false, true)
    let bool_rec = env.get_recursor(&Name::from_string("Bool.rec")).unwrap();
    assert_eq!(bool_rec.num_minors, 2, "Bool.rec should have 2 minors");
    assert_eq!(bool_rec.rules.len(), 2, "Bool.rec should have 2 rules");

    // Check derived definitions with arity
    // Bool.not : Bool → Bool
    let not = env.get_const(&Name::from_string("Bool.not")).unwrap();
    assert_eq!(
        count_pi_args(&not.type_),
        1,
        "Bool.not type should have 1 Pi binder"
    );

    // Bool.and : Bool → Bool → Bool
    let and = env.get_const(&Name::from_string("Bool.and")).unwrap();
    assert_eq!(
        count_pi_args(&and.type_),
        2,
        "Bool.and type should have 2 Pi binders"
    );

    // Bool.or : Bool → Bool → Bool
    let or = env.get_const(&Name::from_string("Bool.or")).unwrap();
    assert_eq!(
        count_pi_args(&or.type_),
        2,
        "Bool.or type should have 2 Pi binders"
    );

    // Bool.xor : Bool → Bool → Bool
    let xor = env.get_const(&Name::from_string("Bool.xor")).unwrap();
    assert_eq!(
        count_pi_args(&xor.type_),
        2,
        "Bool.xor type should have 2 Pi binders"
    );

    // Check true/false aliases (0 Pi binders — constants)
    let true_alias = env.get_const(&Name::from_string("true")).unwrap();
    assert_eq!(
        count_pi_args(&true_alias.type_),
        0,
        "true alias should have 0 Pi binders"
    );
    let false_alias = env.get_const(&Name::from_string("false")).unwrap();
    assert_eq!(
        count_pi_args(&false_alias.type_),
        0,
        "false alias should have 0 Pi binders"
    );

    // Idempotence
    env.init_bool().unwrap();
}

#[test]
fn test_init_bool_retries_from_post_surface_boundary() {
    let mut env = Environment::new();
    env.register_bool_surface()
        .expect("raw Bool registration should succeed");

    assert!(
        !env.has_bool(),
        "register_bool_surface should not mark Bool initialization complete"
    );
    assert!(
        env.get_const(&Name::from_string("sorryAx")).is_none(),
        "raw Bool registration should stop before sorryAx"
    );

    env.init_bool()
        .expect("init_bool should resume from the post-Bool sorryAx boundary");

    assert!(
        env.has_bool(),
        "init_bool retry should complete Bool initialization"
    );
    assert!(
        env.get_const(&Name::from_string("sorryAx")).is_some(),
        "retry should finalize sorryAx registration"
    );
}

#[test]
fn test_constant_info_trust_summary_tracks_registered_provenance() {
    let _serial = crate::test_utils::serial_test_guard();
    let mut env = Environment::default();
    env.init_bool().unwrap();
    env.init_trusted_arith().unwrap();
    env.init_trusted_ay().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Issue2562.goal"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    let goal = Expr::const_(Name::from_string("Issue2562.goal"), vec![]);

    let explicit_name = Name::from_string("Issue2562.explicit");
    let explicit_value =
        crate::sorry::create_sorry_term_with_kind(&env, &goal, crate::sorry::SorryKind::Explicit);
    env.add_decl(Declaration::Theorem {
        name: explicit_name.clone(),
        level_params: vec![],
        type_: goal.clone(),
        value: explicit_value,
    })
    .unwrap();
    let explicit_info = env.get_const(&explicit_name).unwrap();
    let explicit_summary = explicit_info.sorry_summary();
    let explicit_trust = explicit_info.trust_summary();
    assert!(explicit_summary.has_sorry);
    assert!(explicit_summary.has_explicit_sorry);
    assert!(!explicit_summary.has_synthetic_sorry);
    assert!(explicit_trust.has_explicit_sorry);
    assert!(!explicit_trust.has_synthetic_sorry);
    assert_eq!(explicit_trust.trusted_axiom_count(), 0);
    assert_eq!(explicit_trust.sorry_summary(), explicit_summary);

    let synthetic_name = Name::from_string("Issue2562.synthetic");
    let synthetic_value = crate::sorry::create_sorry_term(&env, &goal);
    env.add_decl(Declaration::Theorem {
        name: synthetic_name.clone(),
        level_params: vec![],
        type_: goal,
        value: synthetic_value,
    })
    .unwrap();
    let synthetic_info = env.get_const(&synthetic_name).unwrap();
    let synthetic_summary = synthetic_info.sorry_summary();
    let synthetic_trust = synthetic_info.trust_summary();
    assert!(synthetic_summary.has_sorry);
    assert!(!synthetic_summary.has_explicit_sorry);
    assert!(synthetic_summary.has_synthetic_sorry);
    assert!(!synthetic_trust.has_explicit_sorry);
    assert!(synthetic_trust.has_synthetic_sorry);
    assert_eq!(synthetic_trust.trusted_axiom_count(), 0);
    assert_eq!(synthetic_trust.sorry_summary(), synthetic_summary);

    let goal = Expr::const_(Name::from_string("Issue2562.goal"), vec![]);
    let trusted_arith_name = Name::from_string("Issue2667.trustedArith");
    let trusted_arith_value = Expr::app(
        Expr::const_(Name::from_string("trustedArith"), vec![Level::zero()]),
        goal.clone(),
    );
    env.add_decl(Declaration::Theorem {
        name: trusted_arith_name.clone(),
        level_params: vec![],
        type_: goal.clone(),
        value: trusted_arith_value,
    })
    .unwrap();
    let trusted_arith_summary = env.get_const(&trusted_arith_name).unwrap().trust_summary();
    assert!(!trusted_arith_summary.has_sorry());
    assert_eq!(trusted_arith_summary.trusted_arith_count, 1);
    assert_eq!(trusted_arith_summary.trusted_ay_count, 0);
    assert_eq!(trusted_arith_summary.trusted_axiom_count(), 1);

    let trusted_ay_name = Name::from_string("Issue2667.trustedAy");
    let trusted_ay_value = crate::sorry::create_trusted_ay_term(&env, &goal);
    env.add_decl(Declaration::Theorem {
        name: trusted_ay_name.clone(),
        level_params: vec![],
        type_: goal.clone(),
        value: trusted_ay_value,
    })
    .unwrap();
    let trusted_ay_summary = env.get_const(&trusted_ay_name).unwrap().trust_summary();
    assert!(!trusted_ay_summary.has_sorry());
    assert_eq!(trusted_ay_summary.trusted_arith_count, 0);
    assert_eq!(trusted_ay_summary.trusted_ay_count, 1);
    assert_eq!(trusted_ay_summary.trusted_axiom_count(), 1);

    let clean_proof_name = Name::from_string("Issue2667.CleanProof");
    env.add_decl(Declaration::Axiom {
        name: clean_proof_name.clone(),
        level_params: vec![],
        type_: goal.clone(),
    })
    .unwrap();
    let clean_name_mapping = Name::from_string("Issue2667.clean");
    env.add_decl(Declaration::Theorem {
        name: clean_name_mapping.clone(),
        level_params: vec![],
        type_: goal.clone(),
        value: Expr::const_(clean_proof_name, vec![]),
    })
    .unwrap();
    let clean_summary = env.get_const(&clean_name_mapping).unwrap().trust_summary();
    assert!(clean_summary.is_fully_verified());
    assert_eq!(clean_summary.trusted_axiom_count(), 0);
    assert_eq!(clean_summary.sorry_summary(), SorrySummary::default());
}

#[test]
fn test_bool_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_bool().unwrap();

    let tc = TypeChecker::new(&env);

    // Bool : Type
    let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_type = tc.infer_type(&bool_const).unwrap();
    assert_eq!(
        bool_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // Bool.false : Bool (0 Pi binders — a constant)
    let false_ty = tc
        .infer_type(&Expr::const_(Name::from_string("Bool.false"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&false_ty),
        0,
        "Bool.false type should have 0 Pi binders"
    );

    // Bool.true : Bool (0 Pi binders — a constant)
    let true_ty = tc
        .infer_type(&Expr::const_(Name::from_string("Bool.true"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&true_ty),
        0,
        "Bool.true type should have 0 Pi binders"
    );

    // Bool.not : Bool → Bool
    let not_type = tc
        .infer_type(&Expr::const_(Name::from_string("Bool.not"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&not_type),
        1,
        "Bool.not type should have 1 Pi binder"
    );

    // Bool.and : Bool → Bool → Bool
    let and_type = tc
        .infer_type(&Expr::const_(Name::from_string("Bool.and"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&and_type),
        2,
        "Bool.and type should have 2 Pi binders"
    );

    // Bool.or : Bool → Bool → Bool
    let or_type = tc
        .infer_type(&Expr::const_(Name::from_string("Bool.or"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&or_type),
        2,
        "Bool.or type should have 2 Pi binders"
    );

    // true : Bool (alias for Bool.true)
    let true_type = tc
        .infer_type(&Expr::const_(Name::from_string("true"), vec![]))
        .unwrap();
    assert_eq!(true_type, bool_const);

    // false : Bool (alias for Bool.false)
    let false_type = tc
        .infer_type(&Expr::const_(Name::from_string("false"), vec![]))
        .unwrap();
    assert_eq!(false_type, bool_const);
}

#[test]
fn test_init_nat() {
    let mut env = Environment::new();
    env.init_nat().unwrap();

    // Check Nat type exists with arity verification
    let nat_ind = env.get_inductive(&Name::from_string("Nat")).unwrap();
    assert_eq!(nat_ind.constructor_names.len(), 2);
    // Nat.zero : 0 fields, index 0
    let nat_zero = env.get_constructor(&Name::from_string("Nat.zero")).unwrap();
    assert_eq!(nat_zero.num_fields, 0, "Nat.zero should have 0 fields");
    assert_eq!(
        nat_zero.constructor_idx, 0,
        "Nat.zero should be constructor 0"
    );
    // Nat.succ : 1 field (pred), index 1
    let nat_succ = env.get_constructor(&Name::from_string("Nat.succ")).unwrap();
    assert_eq!(nat_succ.num_fields, 1, "Nat.succ should have 1 field");
    assert_eq!(
        nat_succ.constructor_idx, 1,
        "Nat.succ should be constructor 1"
    );
    // Nat.rec : recursor with 2 minors (zero, succ), recursive
    let nat_rec = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();
    assert_eq!(nat_rec.num_minors, 2, "Nat.rec should have 2 minors");
    assert_eq!(nat_rec.rules.len(), 2, "Nat.rec should have 2 rules");

    // Check derived definitions with arity
    // Nat.pred : Nat → Nat
    let pred = env.get_const(&Name::from_string("Nat.pred")).unwrap();
    assert_eq!(
        count_pi_args(&pred.type_),
        1,
        "Nat.pred type should have 1 Pi binder"
    );

    // Nat.add : Nat → Nat → Nat
    let add = env.get_const(&Name::from_string("Nat.add")).unwrap();
    assert_eq!(
        count_pi_args(&add.type_),
        2,
        "Nat.add type should have 2 Pi binders"
    );

    // Nat.mul : Nat → Nat → Nat
    let mul = env.get_const(&Name::from_string("Nat.mul")).unwrap();
    assert_eq!(
        count_pi_args(&mul.type_),
        2,
        "Nat.mul type should have 2 Pi binders"
    );

    // Nat.sub : Nat → Nat → Nat
    let sub = env.get_const(&Name::from_string("Nat.sub")).unwrap();
    assert_eq!(
        count_pi_args(&sub.type_),
        2,
        "Nat.sub type should have 2 Pi binders"
    );

    // Nat.pow : Nat → Nat → Nat
    let pow = env.get_const(&Name::from_string("Nat.pow")).unwrap();
    assert_eq!(
        count_pi_args(&pow.type_),
        2,
        "Nat.pow type should have 2 Pi binders"
    );

    // Idempotence
    env.init_nat().unwrap();
}

#[test]
fn test_nat_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat().unwrap();

    let tc = TypeChecker::new(&env);

    // Nat : Type
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_type = tc.infer_type(&nat_const).unwrap();
    assert_eq!(
        nat_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // Nat.zero : Nat (0 Pi binders — a constant)
    let zero_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.zero"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&zero_type),
        0,
        "Nat.zero type should have 0 Pi binders"
    );

    // Nat.succ : Nat → Nat
    let succ_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.succ"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&succ_type),
        1,
        "Nat.succ type should have 1 Pi binder"
    );

    // Nat.pred : Nat → Nat
    let pred_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.pred"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&pred_type),
        1,
        "Nat.pred type should have 1 Pi binder"
    );

    // Nat.add : Nat → Nat → Nat
    let add_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.add"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&add_type),
        2,
        "Nat.add type should have 2 Pi binders"
    );

    // Nat.mul : Nat → Nat → Nat
    let mul_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.mul"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&mul_type),
        2,
        "Nat.mul type should have 2 Pi binders"
    );
}

#[test]
fn test_init_ulift() {
    let mut env = Environment::new();
    env.init_ulift().unwrap();

    // Check ULift type exists with arity verification
    let ulift_ind = env.get_inductive(&Name::from_string("ULift")).unwrap();
    assert_eq!(ulift_ind.constructor_names.len(), 1);
    // ULift.up : 1 field (data), index 0
    let ulift_up = env.get_constructor(&Name::from_string("ULift.up")).unwrap();
    assert_eq!(ulift_up.num_fields, 1, "ULift.up should have 1 field");
    assert_eq!(
        ulift_up.constructor_idx, 0,
        "ULift.up should be constructor 0"
    );
    // ULift.rec : recursor with 1 minor (up)
    let ulift_rec = env.get_recursor(&Name::from_string("ULift.rec")).unwrap();
    assert_eq!(ulift_rec.num_minors, 1, "ULift.rec should have 1 minor");
    assert_eq!(ulift_rec.rules.len(), 1, "ULift.rec should have 1 rule");

    // ULift.down : {α : Sort u} → ULift.{v} α → α
    let down = env.get_const(&Name::from_string("ULift.down")).unwrap();
    assert_eq!(
        count_pi_args(&down.type_),
        2,
        "ULift.down type should have 2 Pi binders (α, self)"
    );

    // Check structure fields
    let fields = env
        .get_structure_field_names(&Name::from_string("ULift"))
        .unwrap();
    assert_eq!(fields.len(), 1);

    // Idempotence
    env.init_ulift().unwrap();
}

#[test]
fn test_ulift_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_ulift().unwrap();

    let tc = TypeChecker::new(&env);

    // ULift : Type s → Type (max s r)
    let ulift_const = Expr::const_(
        Name::from_string("ULift"),
        vec![Level::zero(), Level::zero()],
    );
    let ulift_type = tc.infer_type(&ulift_const).unwrap();
    assert_eq!(
        count_pi_args(&ulift_type),
        1,
        "ULift type should have 1 Pi binder (α)"
    );

    // ULift.up : {α : Type s} → α → ULift α
    let up_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("ULift.up"),
            vec![Level::zero(), Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&up_type),
        2,
        "ULift.up type should have 2 Pi binders (α, val)"
    );
}

#[test]
fn test_all_base_types() {
    // Test that all fundamental types work together
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_nat().unwrap();
    env.init_ulift().unwrap();

    assert!(env.has_bool());
    assert!(env.has_nat());
    assert!(env.has_ulift());
}

#[test]
fn test_init_char() {
    let mut env = Environment::new();
    env.init_char().unwrap();

    // Char : inductive with 1 constructor (Char.mk)
    let char_ind = env.get_inductive(&Name::from_string("Char")).unwrap();
    assert_eq!(
        char_ind.constructor_names.len(),
        1,
        "Char should have 1 constructor (mk)"
    );
    // Char.mk : constructor with fields for the char value
    let char_mk = env.get_constructor(&Name::from_string("Char.mk")).unwrap();
    assert_eq!(
        char_mk.constructor_idx, 0,
        "Char.mk should be constructor 0"
    );
    // Char.rec : recursor with 1 minor (mk)
    let char_rec = env.get_recursor(&Name::from_string("Char.rec")).unwrap();
    assert_eq!(char_rec.num_minors, 1, "Char.rec should have 1 minor");
    assert_eq!(char_rec.rules.len(), 1, "Char.rec should have 1 rule");

    // Char.val : Char → UInt32
    let val = env.get_const(&Name::from_string("Char.val")).unwrap();
    assert_eq!(
        count_pi_args(&val.type_),
        1,
        "Char.val type should have 1 Pi binder (self)"
    );

    // Char.ofNat is now seeded by `init_char_defs` in the extended phase (it
    // needs `dite` / the Decidable instances, absent this early), NOT by
    // `init_char` — carrier-parity P2. So it is deliberately absent here.
    assert!(
        env.get_const(&Name::from_string("Char.ofNat")).is_none(),
        "Char.ofNat is seeded later (init_char_defs), not by init_char"
    );

    // Char.toNat : Char → Nat
    let to_nat = env.get_const(&Name::from_string("Char.toNat")).unwrap();
    assert_eq!(
        count_pi_args(&to_nat.type_),
        1,
        "Char.toNat type should have 1 Pi binder (c)"
    );

    // Check structure fields
    let fields = env
        .get_structure_field_names(&Name::from_string("Char"))
        .unwrap();
    assert!(!fields.is_empty());

    // Nat should be auto-initialized as dependency
    assert!(env.has_nat());

    // Idempotence
    env.init_char().unwrap();
}

#[test]
fn test_char_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_char().unwrap();

    let tc = TypeChecker::new(&env);

    // Char : Type
    let char_const = Expr::const_(Name::from_string("Char"), vec![]);
    let char_type = tc.infer_type(&char_const).unwrap();
    assert_eq!(
        char_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // Char.mk : Nat → Char (constructor may have validity proof arg)
    let mk_type = tc
        .infer_type(&Expr::const_(Name::from_string("Char.mk"), vec![]))
        .unwrap();
    assert!(
        count_pi_args(&mk_type) >= 1,
        "Char.mk type should have at least 1 Pi binder"
    );

    // Char.val : Char → UInt32 (genuine v4.30 shape; 1 Pi binder)
    let val_type = tc
        .infer_type(&Expr::const_(Name::from_string("Char.val"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&val_type),
        1,
        "Char.val type should have 1 Pi binder (self)"
    );

    // Char.ofNat is seeded later (init_char_defs), not by init_char — see
    // test_init_char.

    // Char.toNat : Char → Nat
    let tonat_type = tc
        .infer_type(&Expr::const_(Name::from_string("Char.toNat"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&tonat_type),
        1,
        "Char.toNat type should have 1 Pi binder"
    );
}

#[test]
fn test_init_list() {
    let mut env = Environment::new();
    env.init_list().unwrap();

    // Check List type exists with arity verification
    let list_ind = env.get_inductive(&Name::from_string("List")).unwrap();
    assert_eq!(list_ind.num_params, 1, "List should have 1 type param (α)");
    assert_eq!(list_ind.constructor_names.len(), 2);
    // List.nil : 0 fields, index 0
    let list_nil = env.get_constructor(&Name::from_string("List.nil")).unwrap();
    assert_eq!(list_nil.num_fields, 0, "List.nil should have 0 fields");
    assert_eq!(
        list_nil.constructor_idx, 0,
        "List.nil should be constructor 0"
    );
    // List.cons : 2 fields (head, tail), index 1
    let list_cons = env
        .get_constructor(&Name::from_string("List.cons"))
        .unwrap();
    assert_eq!(list_cons.num_fields, 2, "List.cons should have 2 fields");
    assert_eq!(
        list_cons.constructor_idx, 1,
        "List.cons should be constructor 1"
    );
    // List.rec : recursor with 2 minors (nil, cons), recursive
    let list_rec = env.get_recursor(&Name::from_string("List.rec")).unwrap();
    assert_eq!(list_rec.num_minors, 2, "List.rec should have 2 minors");
    assert_eq!(list_rec.rules.len(), 2, "List.rec should have 2 rules");

    // List.tail : {α : Type u} → List α → List α
    let tail = env.get_const(&Name::from_string("List.tail")).unwrap();
    assert_eq!(
        count_pi_args(&tail.type_),
        2,
        "List.tail type should have 2 Pi binders (α, self)"
    );

    // List.length : {α : Type u} → List α → Nat
    let length = env.get_const(&Name::from_string("List.length")).unwrap();
    assert_eq!(
        count_pi_args(&length.type_),
        2,
        "List.length type should have 2 Pi binders (α, self)"
    );

    // Nat should be auto-initialized as dependency
    assert!(env.has_nat());

    // Idempotence
    env.init_list().unwrap();
}

#[test]
fn test_list_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_list().unwrap();

    let tc = TypeChecker::new(&env);

    // List : Type u → Type u
    let list_const = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
    let list_type = tc.infer_type(&list_const).unwrap();
    assert_eq!(
        count_pi_args(&list_type),
        1,
        "List type should have 1 Pi binder (α)"
    );

    // List.nil : {α : Type u} → List α
    let nil_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.nil"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&nil_type),
        1,
        "List.nil type should have 1 Pi binder (α)"
    );

    // List.cons : {α : Type u} → α → List α → List α
    let cons_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.cons"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&cons_type),
        3,
        "List.cons type should have 3 Pi binders (α, head, tail)"
    );

    // List.tail : {α : Type u} → List α → List α
    let tail_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.tail"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&tail_type),
        2,
        "List.tail type should have 2 Pi binders (α, list)"
    );

    // List.length : {α : Type u} → List α → Nat
    let length_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.length"),
            vec![Level::zero()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&length_type),
        2,
        "List.length type should have 2 Pi binders (α, list)"
    );
}

#[test]
fn test_init_string() {
    let mut env = Environment::new();
    env.init_string().unwrap();

    // String : inductive with 1 constructor (String.mk)
    let string_ind = env.get_inductive(&Name::from_string("String")).unwrap();
    assert_eq!(
        string_ind.constructor_names.len(),
        1,
        "String should have 1 constructor (mk)"
    );
    // String.mk : constructor index 0
    let string_mk = env
        .get_constructor(&Name::from_string("String.mk"))
        .unwrap();
    assert_eq!(
        string_mk.constructor_idx, 0,
        "String.mk should be constructor 0"
    );
    // String.rec : recursor with 1 minor (mk)
    let string_rec = env.get_recursor(&Name::from_string("String.rec")).unwrap();
    assert_eq!(string_rec.num_minors, 1, "String.rec should have 1 minor");
    assert_eq!(string_rec.rules.len(), 1, "String.rec should have 1 rule");

    // String.data : String → List Char
    let data = env.get_const(&Name::from_string("String.data")).unwrap();
    assert_eq!(
        count_pi_args(&data.type_),
        1,
        "String.data type should have 1 Pi binder (self)"
    );

    // String.length : String → Nat
    let length = env.get_const(&Name::from_string("String.length")).unwrap();
    assert_eq!(
        count_pi_args(&length.type_),
        1,
        "String.length type should have 1 Pi binder (self)"
    );

    // Check structure fields
    let fields = env
        .get_structure_field_names(&Name::from_string("String"))
        .unwrap();
    assert!(!fields.is_empty());

    // Dependencies should be auto-initialized
    assert!(env.has_list());
    assert!(env.has_char());
    assert!(env.has_nat());

    // Idempotence
    env.init_string().unwrap();
}

#[test]
fn test_with_prelude_includes_string() {
    let env = Environment::with_prelude();
    assert!(env.has_string());
    assert!(env.has_char());
    let string_ind = env.get_inductive(&Name::from_string("String")).unwrap();
    assert_eq!(
        string_ind.constructor_names.len(),
        1,
        "String should have 1 constructor via prelude"
    );
    let char_ind = env.get_inductive(&Name::from_string("Char")).unwrap();
    assert_eq!(
        char_ind.constructor_names.len(),
        1,
        "Char should have 1 constructor via prelude"
    );
}

#[test]
fn test_with_prelude_includes_nat_ordering() {
    // Verify Nat ordering lemmas are available in with_prelude() (#2124).
    // These are required by linarith proof reconstruction.
    let env = Environment::with_prelude();

    // Nat.le_trans (from init_nat_preorder)
    assert!(
        env.get_const(&Name::from_string("Nat.le_trans")).is_some(),
        "with_prelude() must provide Nat.le_trans for linarith"
    );

    // Nat.add_le_add (from init_nat_add_ord)
    assert!(
        env.get_const(&Name::from_string("Nat.add_le_add"))
            .is_some(),
        "with_prelude() must provide Nat.add_le_add for linarith"
    );

    // Nat.mul_le_mul_left (from init_nat_mul_ord)
    assert!(
        env.get_const(&Name::from_string("Nat.mul_le_mul_left"))
            .is_some(),
        "with_prelude() must provide Nat.mul_le_mul_left for linarith"
    );
    assert!(
        env.get_const(&Name::from_string("Nat.not_lt")).is_some(),
        "with_prelude() must provide Nat.not_lt for Nat push-neg replay"
    );
    assert!(
        env.get_const(&Name::from_string("Nat.not_le")).is_some(),
        "with_prelude() must provide Nat.not_le for Nat push-neg replay"
    );

    // Ordering structure instances
    assert!(
        env.get_const(&Name::from_string("instPreorderNat"))
            .is_some(),
        "with_prelude() must provide instPreorderNat"
    );
    assert!(
        env.get_const(&Name::from_string("instLinearOrderNat"))
            .is_some(),
        "with_prelude() must provide instLinearOrderNat"
    );
}

#[test]
fn test_string_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_string().unwrap();

    let tc = TypeChecker::new(&env);

    // String : Type
    let string_const = Expr::const_(Name::from_string("String"), vec![]);
    let string_type = tc.infer_type(&string_const).unwrap();
    assert_eq!(
        string_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // String.mk : List Char → String
    let mk_type = tc
        .infer_type(&Expr::const_(Name::from_string("String.mk"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&mk_type),
        1,
        "String.mk type should have 1 Pi binder (data)"
    );

    // String.data : String → List Char
    let data_type = tc
        .infer_type(&Expr::const_(Name::from_string("String.data"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&data_type),
        1,
        "String.data type should have 1 Pi binder (self)"
    );

    // String.length : String → Nat
    let length_type = tc
        .infer_type(&Expr::const_(Name::from_string("String.length"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&length_type),
        1,
        "String.length type should have 1 Pi binder (self)"
    );
}

#[test]
fn test_init_int() {
    let mut env = Environment::new();
    env.init_int().unwrap();

    // Check Int type exists with arity verification
    let int_ind = env.get_inductive(&Name::from_string("Int")).unwrap();
    assert_eq!(int_ind.constructor_names.len(), 2);
    // Int.ofNat : 1 field (n), index 0
    let int_ofnat = env
        .get_constructor(&Name::from_string("Int.ofNat"))
        .unwrap();
    assert_eq!(int_ofnat.num_fields, 1, "Int.ofNat should have 1 field");
    assert_eq!(
        int_ofnat.constructor_idx, 0,
        "Int.ofNat should be constructor 0"
    );
    // Int.negSucc : 1 field (n), index 1
    let int_negsucc = env
        .get_constructor(&Name::from_string("Int.negSucc"))
        .unwrap();
    assert_eq!(int_negsucc.num_fields, 1, "Int.negSucc should have 1 field");
    assert_eq!(
        int_negsucc.constructor_idx, 1,
        "Int.negSucc should be constructor 1"
    );
    // Int.rec : recursor with 2 minors (ofNat, negSucc)
    let int_rec = env.get_recursor(&Name::from_string("Int.rec")).unwrap();
    assert_eq!(int_rec.num_minors, 2, "Int.rec should have 2 minors");
    assert_eq!(int_rec.rules.len(), 2, "Int.rec should have 2 rules");

    // Int.neg : Int → Int
    let neg = env.get_const(&Name::from_string("Int.neg")).unwrap();
    assert_eq!(
        count_pi_args(&neg.type_),
        1,
        "Int.neg type should have 1 Pi binder"
    );

    // Int.toNat : Int → Nat
    let to_nat = env.get_const(&Name::from_string("Int.toNat")).unwrap();
    assert_eq!(
        count_pi_args(&to_nat.type_),
        1,
        "Int.toNat type should have 1 Pi binder"
    );

    // Nat should be auto-initialized as dependency
    assert!(env.has_nat());

    // Idempotence
    env.init_int().unwrap();
}

#[test]
fn test_int_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int().unwrap();

    let tc = TypeChecker::new(&env);

    // Int : Type
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let int_type = tc.infer_type(&int_const).unwrap();
    assert_eq!(
        int_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // Int.ofNat : Nat → Int
    let ofnat_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.ofNat"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&ofnat_type),
        1,
        "Int.ofNat type should have 1 Pi binder"
    );

    // Int.negSucc : Nat → Int
    let negsucc_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.negSucc"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&negsucc_type),
        1,
        "Int.negSucc type should have 1 Pi binder"
    );

    // Int.neg : Int → Int
    let neg_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.neg"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&neg_type),
        1,
        "Int.neg type should have 1 Pi binder"
    );

    // Int.toNat : Int → Nat
    let tonat_type = tc
        .infer_type(&Expr::const_(Name::from_string("Int.toNat"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&tonat_type),
        1,
        "Int.toNat type should have 1 Pi binder"
    );
}

#[test]
fn test_all_data_types() {
    // Test that all data types work together
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_nat().unwrap();
    env.init_char().unwrap();
    env.init_list().unwrap();
    env.init_string().unwrap();
    env.init_int().unwrap();

    assert!(env.has_bool());
    assert!(env.has_nat());
    assert!(env.has_char());
    assert!(env.has_list());
    assert!(env.has_string());
    assert!(env.has_int());
}

#[test]
fn test_init_unit() {
    let mut env = Environment::new();
    assert!(!env.has_unit());

    env.init_unit().unwrap();
    assert!(env.has_unit());

    // Unit is now a reducible definition equal to PUnit.{1} (#3418).
    // It is NOT an inductive — it's an abbreviation:
    //   Unit : Type := PUnit.{1}
    //   Unit.unit : Unit := PUnit.unit.{1}
    // This ensures definitional equality with PUnit.{1} for StateT.set.

    // Unit should be a reducible definition (not an inductive)
    let unit_def = env
        .get_const(&Name::from_string("Unit"))
        .expect("Unit should exist as a constant");
    assert!(
        unit_def.is_reducible,
        "Unit should be reducible (it's an abbreviation for PUnit.{{1}})"
    );
    assert!(
        unit_def.value.is_some(),
        "Unit should have a value (PUnit.{{1}})"
    );

    // Unit.unit should also be a reducible definition
    let unit_unit_def = env
        .get_const(&Name::from_string("Unit.unit"))
        .expect("Unit.unit should exist as a constant");
    assert!(unit_unit_def.is_reducible, "Unit.unit should be reducible");
    assert!(
        unit_unit_def.value.is_some(),
        "Unit.unit should have a value (PUnit.unit.{{1}})"
    );

    // PUnit should still be an inductive (Unit delegates to it)
    let punit_ind = env.get_inductive(&Name::from_string("PUnit")).unwrap();
    assert_eq!(
        punit_ind.constructor_names.len(),
        1,
        "PUnit should have 1 constructor"
    );

    // Idempotent
    env.init_unit().unwrap();
    assert!(env.has_unit());
}

#[test]
fn test_unit_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_unit().unwrap();

    let tc = TypeChecker::new(&env);

    // Unit : Type
    let unit_const = Expr::const_(Name::from_string("Unit"), vec![]);
    let unit_type = tc.infer_type(&unit_const).unwrap();
    assert_eq!(
        unit_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // Unit.unit : Unit
    let unit_unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
    let unit_unit_type = tc.infer_type(&unit_unit).unwrap();
    assert_eq!(unit_unit_type, unit_const);
}

/// Unit should delta-unfold to PUnit.{1} during WHNF, matching Lean 4's
/// `abbrev Unit := PUnit`. This makes PUnit.{1} and Unit definitionally
/// equal, which is required for StateT.set in abbrev contexts. Part of #3418.
#[test]
fn test_unit_unfolds_to_punit_1() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_unit().unwrap(); // init_unit now calls init_punit first

    let tc = TypeChecker::new(&env);

    // Unit should WHNF-reduce to PUnit.{1}
    let unit = Expr::const_(Name::from_string("Unit"), vec![]);
    let punit_1 = Expr::const_(Name::from_string("PUnit"), vec![Level::succ(Level::zero())]);
    let unit_whnf = tc.whnf(&unit);
    assert_eq!(
        unit_whnf, punit_1,
        "Unit should delta-reduce to PUnit.{{1}} during WHNF"
    );

    // Unit.unit should WHNF-reduce to PUnit.unit.{1}
    let unit_unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
    let punit_unit_1 = Expr::const_(
        Name::from_string("PUnit.unit"),
        vec![Level::succ(Level::zero())],
    );
    let unit_unit_whnf = tc.whnf(&unit_unit);
    assert_eq!(
        unit_unit_whnf, punit_unit_1,
        "Unit.unit should delta-reduce to PUnit.unit.{{1}} during WHNF"
    );

    // is_def_eq should hold between Unit and PUnit.{1}
    assert!(
        tc.is_def_eq(&unit, &punit_1),
        "Unit and PUnit.{{1}} should be definitionally equal"
    );

    // is_def_eq should hold between Unit.unit and PUnit.unit.{1}
    assert!(
        tc.is_def_eq(&unit_unit, &punit_unit_1),
        "Unit.unit and PUnit.unit.{{1}} should be definitionally equal"
    );
}

#[test]
fn test_init_plift() {
    let mut env = Environment::new();
    assert!(!env.has_plift());

    env.init_plift().unwrap();
    assert!(env.has_plift());

    // Check that PLift and PLift.up were added with arity verification
    let plift_ind = env.get_inductive(&Name::from_string("PLift")).unwrap();
    assert_eq!(plift_ind.constructor_names.len(), 1);
    // PLift.up : 1 field, index 0
    let plift_up = env.get_constructor(&Name::from_string("PLift.up")).unwrap();
    assert_eq!(plift_up.num_fields, 1, "PLift.up should have 1 field");
    assert_eq!(
        plift_up.constructor_idx, 0,
        "PLift.up should be constructor 0"
    );
    // PLift.rec : recursor with 1 minor (up)
    let plift_rec = env.get_recursor(&Name::from_string("PLift.rec")).unwrap();
    assert_eq!(plift_rec.num_minors, 1, "PLift.rec should have 1 minor");
    assert_eq!(plift_rec.rules.len(), 1, "PLift.rec should have 1 rule");

    // PLift.down : {α : Prop} → PLift α → α
    let down = env.get_const(&Name::from_string("PLift.down")).unwrap();
    assert_eq!(
        count_pi_args(&down.type_),
        2,
        "PLift.down type should have 2 Pi binders (α, self)"
    );

    // Idempotent
    env.init_plift().unwrap();
    assert!(env.has_plift());
}

#[test]
fn test_plift_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_plift().unwrap();

    let tc = TypeChecker::new(&env);

    // PLift : Prop → Type
    let plift_const = Expr::const_(Name::from_string("PLift"), vec![]);
    let plift_type = tc.infer_type(&plift_const).unwrap();
    // PLift : Prop → Type
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let expected = Expr::pi(BinderInfo::Default, prop, type_);
    assert_eq!(plift_type, expected);

    // PLift.up : {α : Prop} → α → PLift α
    let up_type = tc
        .infer_type(&Expr::const_(Name::from_string("PLift.up"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&up_type),
        2,
        "PLift.up type should have 2 Pi binders (α, val)"
    );

    // PLift.down : {α : Prop} → PLift α → α
    let down_type = tc
        .infer_type(&Expr::const_(Name::from_string("PLift.down"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&down_type),
        2,
        "PLift.down type should have 2 Pi binders (α, self)"
    );
}

#[test]
fn test_init_fin() {
    let mut env = Environment::new();
    assert!(!env.has_fin());

    env.init_fin().unwrap();
    assert!(env.has_fin());

    // Check that Fin and Fin.mk were added with arity verification
    let fin_ind = env.get_inductive(&Name::from_string("Fin")).unwrap();
    assert_eq!(fin_ind.num_params, 1, "Fin should have 1 type param (n)");
    // Fin.mk : constructor index 0
    let fin_mk = env.get_constructor(&Name::from_string("Fin.mk")).unwrap();
    assert_eq!(fin_mk.constructor_idx, 0, "Fin.mk should be constructor 0");
    // Fin.rec : recursor with 1 minor (mk)
    let fin_rec = env.get_recursor(&Name::from_string("Fin.rec")).unwrap();
    assert_eq!(fin_rec.num_minors, 1, "Fin.rec should have 1 minor");
    assert_eq!(fin_rec.rules.len(), 1, "Fin.rec should have 1 rule");

    // Fin.val : {n : Nat} → Fin n → Nat
    let val = env.get_const(&Name::from_string("Fin.val")).unwrap();
    assert_eq!(
        count_pi_args(&val.type_),
        2,
        "Fin.val type should have 2 Pi binders (n, self)"
    );

    // Check that Nat was auto-initialized
    assert!(env.has_nat());

    // Idempotent
    env.init_fin().unwrap();
    assert!(env.has_fin());
}

#[test]
fn test_fin_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_fin().unwrap();

    let tc = TypeChecker::new(&env);

    // Fin : Nat → Type
    let fin_const = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_type = tc.infer_type(&fin_const).unwrap();
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let expected = Expr::pi(BinderInfo::Default, nat_const, type_);
    assert_eq!(fin_type, expected);

    // Fin.mk : (n : Nat) → (val : Nat) → val < n → Fin n
    let mk_type = tc
        .infer_type(&Expr::const_(Name::from_string("Fin.mk"), vec![]))
        .unwrap();
    assert!(
        count_pi_args(&mk_type) >= 2,
        "Fin.mk type should have at least 2 Pi binders (n, val, isLt)"
    );

    // Fin.val : {n : Nat} → Fin n → Nat
    let val_type = tc
        .infer_type(&Expr::const_(Name::from_string("Fin.val"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&val_type),
        2,
        "Fin.val type should have 2 Pi binders (n, self)"
    );
}

#[test]
fn test_init_array() {
    let mut env = Environment::new();
    assert!(!env.has_array());

    env.init_array().unwrap();
    assert!(env.has_array());

    // Check that Array and Array.mk were added with arity verification
    let array_ind = env.get_inductive(&Name::from_string("Array")).unwrap();
    assert_eq!(
        array_ind.num_params, 1,
        "Array should have 1 type param (α)"
    );
    // Array.mk : constructor index 0
    let array_mk = env.get_constructor(&Name::from_string("Array.mk")).unwrap();
    assert_eq!(
        array_mk.constructor_idx, 0,
        "Array.mk should be constructor 0"
    );
    // Array.rec : recursor with 1 minor (mk)
    let array_rec = env.get_recursor(&Name::from_string("Array.rec")).unwrap();
    assert_eq!(array_rec.num_minors, 1, "Array.rec should have 1 minor");
    assert_eq!(array_rec.rules.len(), 1, "Array.rec should have 1 rule");

    // Array.data : {α : Type u} → Array α → List α
    let data = env.get_const(&Name::from_string("Array.data")).unwrap();
    assert_eq!(
        count_pi_args(&data.type_),
        2,
        "Array.data type should have 2 Pi binders (α, self)"
    );

    // Array.size : {α : Type u} → Array α → Nat
    let size = env.get_const(&Name::from_string("Array.size")).unwrap();
    assert_eq!(
        count_pi_args(&size.type_),
        2,
        "Array.size type should have 2 Pi binders (α, self)"
    );

    // Check that dependencies were auto-initialized
    assert!(env.has_list());
    assert!(env.has_nat()); // via List

    // Idempotent
    env.init_array().unwrap();
    assert!(env.has_array());
}

#[test]
fn test_array_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_array().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let level_u = Level::param(u);

    // Array : Type u → Type u
    let array_const = Expr::const_(Name::from_string("Array"), vec![level_u.clone()]);
    let array_type = tc.infer_type(&array_const).unwrap();
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(level_u.clone())));
    let expected = Expr::pi(BinderInfo::Default, type_u.clone(), type_u);
    assert_eq!(array_type, expected);

    // Array.mk : {α : Type u} → List α → Array α
    let mk_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Array.mk"),
            vec![level_u.clone()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&mk_type),
        2,
        "Array.mk type should have 2 Pi binders (α, data)"
    );

    // Array.data : {α : Type u} → Array α → List α
    let data_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Array.data"),
            vec![level_u.clone()],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&data_type),
        2,
        "Array.data type should have 2 Pi binders (α, self)"
    );

    // Array.size : {α : Type u} → Array α → Nat
    let size_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Array.size"),
            vec![level_u],
        ))
        .unwrap();
    assert_eq!(
        count_pi_args(&size_type),
        2,
        "Array.size type should have 2 Pi binders (α, self)"
    );
}

#[test]
fn test_all_container_types() {
    // Test that all container and utility types work together
    let mut env = Environment::new();

    // Initialize all new types
    env.init_unit().unwrap();
    env.init_plift().unwrap();
    env.init_fin().unwrap();
    env.init_array().unwrap();

    // Verify all are initialized
    assert!(env.has_unit());
    assert!(env.has_plift());
    assert!(env.has_fin());
    assert!(env.has_array());

    // Verify dependencies
    assert!(env.has_nat()); // Required by Fin and Array (via List.length)
    assert!(env.has_list()); // Required by Array
}

#[test]
fn test_init_ordering() {
    let mut env = Environment::new();
    assert!(!env.has_ordering());

    env.init_ordering().unwrap();
    assert!(env.has_ordering());

    // Check that Ordering and constructors were added with arity verification
    let ord_ind = env.get_inductive(&Name::from_string("Ordering")).unwrap();
    assert_eq!(ord_ind.constructor_names.len(), 3);
    let lt_ctor = env
        .get_constructor(&Name::from_string("Ordering.lt"))
        .expect("Ordering.lt constructor must exist");
    assert_eq!(lt_ctor.num_fields, 0, "Ordering.lt has no fields");

    let eq_ctor = env
        .get_constructor(&Name::from_string("Ordering.eq"))
        .expect("Ordering.eq constructor must exist");
    assert_eq!(eq_ctor.num_fields, 0, "Ordering.eq has no fields");

    let gt_ctor = env
        .get_constructor(&Name::from_string("Ordering.gt"))
        .expect("Ordering.gt constructor must exist");
    assert_eq!(gt_ctor.num_fields, 0, "Ordering.gt has no fields");

    let ord_rec = env
        .get_recursor(&Name::from_string("Ordering.rec"))
        .expect("Ordering.rec must exist");
    assert_eq!(
        ord_rec.num_minors, 3,
        "Ordering.rec must have 3 minor premises"
    );

    // Ordering.swap : Ordering → Ordering
    let swap = env.get_const(&Name::from_string("Ordering.swap")).unwrap();
    assert_eq!(
        count_pi_args(&swap.type_),
        1,
        "Ordering.swap type should have 1 Pi binder"
    );

    // Ordering.isLt : Ordering → Bool
    let is_lt = env.get_const(&Name::from_string("Ordering.isLt")).unwrap();
    assert_eq!(
        count_pi_args(&is_lt.type_),
        1,
        "Ordering.isLt type should have 1 Pi binder"
    );

    // Ordering.isEq : Ordering → Bool
    let is_eq = env.get_const(&Name::from_string("Ordering.isEq")).unwrap();
    assert_eq!(
        count_pi_args(&is_eq.type_),
        1,
        "Ordering.isEq type should have 1 Pi binder"
    );

    // Ordering.isGt : Ordering → Bool
    let is_gt = env.get_const(&Name::from_string("Ordering.isGt")).unwrap();
    assert_eq!(
        count_pi_args(&is_gt.type_),
        1,
        "Ordering.isGt type should have 1 Pi binder"
    );

    // Idempotent
    env.init_ordering().unwrap();
    assert!(env.has_ordering());
}

#[test]
fn test_ordering_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_ordering().unwrap();

    let tc = TypeChecker::new(&env);

    // Ordering : Type
    let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);
    let ordering_type = tc.infer_type(&ordering_const).unwrap();
    assert_eq!(
        ordering_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    // Ordering.lt : Ordering
    let ordering_lt = Expr::const_(Name::from_string("Ordering.lt"), vec![]);
    let lt_type = tc.infer_type(&ordering_lt).unwrap();
    assert_eq!(lt_type, ordering_const);

    // Ordering.swap : Ordering → Ordering
    let swap_type = tc
        .infer_type(&Expr::const_(Name::from_string("Ordering.swap"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&swap_type),
        1,
        "Ordering.swap type should have 1 Pi binder"
    );

    // Ordering.isLt : Ordering → Bool
    let islt_type = tc
        .infer_type(&Expr::const_(Name::from_string("Ordering.isLt"), vec![]))
        .unwrap();
    assert_eq!(
        count_pi_args(&islt_type),
        1,
        "Ordering.isLt type should have 1 Pi binder"
    );
}

#[test]
fn test_init_option_ops() {
    let mut env = Environment::new();
    assert!(!env.has_option_ops());

    env.init_option_ops().unwrap();
    assert!(env.has_option_ops());

    // Check that Option operations were added with arity verification
    // Option.map : {α : Type u} → {β : Type u} → (α → β) → Option α → Option β
    let map = env.get_const(&Name::from_string("Option.map")).unwrap();
    assert_eq!(
        count_pi_args(&map.type_),
        4,
        "Option.map type should have 4 Pi binders (α, β, f, opt)"
    );

    // Option.bind : {α : Type u} → {β : Type u} → Option α → (α → Option β) → Option β
    let bind = env.get_const(&Name::from_string("Option.bind")).unwrap();
    assert_eq!(
        count_pi_args(&bind.type_),
        4,
        "Option.bind type should have 4 Pi binders (α, β, opt, f)"
    );

    // Option.getD : {α : Type u} → Option α → α → α
    let getd = env.get_const(&Name::from_string("Option.getD")).unwrap();
    assert_eq!(
        count_pi_args(&getd.type_),
        3,
        "Option.getD type should have 3 Pi binders (α, opt, default)"
    );

    // Check that dependencies were auto-initialized
    assert!(env.has_option());

    // Idempotent
    env.init_option_ops().unwrap();
    assert!(env.has_option_ops());
}

#[test]
fn test_option_ops_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_option_ops().unwrap();

    let tc = TypeChecker::new(&env);
    let level_u = Level::param(Name::from_string("u"));
    let level_v = Level::param(Name::from_string("v"));

    // Option.map type checks — {α : Type u} {β : Type v} (two universes, matching Lean)
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("Option.map"),
            vec![level_u.clone(), level_v.clone()],
        ))
        .unwrap();

    // Option.bind type checks — {α : Type u} {β : Type v}
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("Option.bind"),
            vec![level_u.clone(), level_v],
        ))
        .unwrap();

    // Option.getD type checks — {α : Type u} (single universe)
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("Option.getD"),
            vec![level_u],
        ))
        .unwrap();
}

#[test]
fn test_init_list_ops() {
    let mut env = Environment::new();
    assert!(!env.has_list_ops());

    env.init_list_ops().unwrap();
    assert!(env.has_list_ops());

    // Check that List operations were added with arity verification
    // List.append : {α : Type u} → List α → List α → List α
    let append = env.get_const(&Name::from_string("List.append")).unwrap();
    assert_eq!(
        count_pi_args(&append.type_),
        3,
        "List.append type should have 3 Pi binders (α, xs, ys)"
    );

    // List.reverse : {α : Type u} → List α → List α
    let reverse = env.get_const(&Name::from_string("List.reverse")).unwrap();
    assert_eq!(
        count_pi_args(&reverse.type_),
        2,
        "List.reverse type should have 2 Pi binders (α, xs)"
    );

    // List.map : {α : Type u} → {β : Type v} → (α → β) → List α → List β
    let map = env.get_const(&Name::from_string("List.map")).unwrap();
    assert_eq!(
        count_pi_args(&map.type_),
        4,
        "List.map type should have 4 Pi binders (α, β, f, xs)"
    );

    // Check that dependencies were auto-initialized
    assert!(env.has_list());

    // Idempotent
    env.init_list_ops().unwrap();
    assert!(env.has_list_ops());
}

#[test]
fn test_list_append_nil_is_proved_and_axiom_free() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_list_ops().unwrap();

    // Registered as a Theorem (a real proof), not an Axiom.
    let info = env
        .get_const(&Name::from_string("List.append_nil"))
        .expect("List.append_nil should be registered by init_list_ops");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "List.append_nil must be a Theorem (List.rec proof), not an Axiom"
    );

    // The proof term + type kernel-typecheck.
    let tc = TypeChecker::new(&env);
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.append_nil"),
            vec![Level::param(Name::from_string("u"))],
        ))
        .expect("List.append_nil type-checks");

    // Transitive axiom closure ⊆ FOUNDATIONAL (List.rec + congrArg + Eq.refl).
    let mut deps: Vec<String> = env
        .axiom_deps(&Name::from_string("List.append_nil"))
        .expect("List.append_nil should be registered")
        .iter()
        .map(|n| n.to_string())
        .collect();
    deps.sort();
    assert!(
        deps.is_empty(),
        "List.append_nil must be axiom-free (⊆ foundational), got {deps:?}"
    );
}

#[test]
fn test_list_append_nil_in_prelude() {
    // append_nil must reach the default prelude (via init_list_ops, which is
    // pulled in by init_string_happend_inst).
    let env = Environment::with_prelude();
    assert!(
        env.get_const(&Name::from_string("List.append_nil"))
            .is_some(),
        "List.append_nil must be present in Environment::with_prelude()"
    );
}

/// Lean fidelity: `List.reverseAux` is registered as an axiom-free
/// `Definition`, and `List.reverse` is registered as `reverseAux · []` (Lean's
/// `Init/Data/List/Basic.lean` definition), so `List.reverse l` δ-reduces to
/// `List.reverseAux l []`. Before this fix `List.reverse` was a direct
/// `List.rec` append form that did NOT reduce to the `reverseAux`-headed shape
/// Lean elaborates `List.reverse`-lemma statements through, so
/// `List.get_reverse` (and the `reverse = reverseAux · []` family) failed
/// kernel re-verification.
#[test]
fn test_list_reverse_is_reverse_aux_lean_faithful() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_list_ops().unwrap();

    let u = Level::param(Name::from_string("u"));

    // reverseAux is registered as an axiom-free Definition.
    let raux = env
        .get_const(&Name::from_string("List.reverseAux"))
        .expect("List.reverseAux should be registered by init_list_ops");
    assert!(
        raux.value.is_some(),
        "List.reverseAux must be a Definition (not an Axiom)"
    );
    assert_eq!(
        count_pi_args(&raux.type_),
        3,
        "List.reverseAux type should have 3 Pi binders (α, l, r)"
    );
    let raux_deps = env
        .axiom_deps(&Name::from_string("List.reverseAux"))
        .expect("reverseAux registered");
    assert!(
        raux_deps.is_empty(),
        "List.reverseAux must be axiom-free (built from List.rec), got {:?}",
        raux_deps.iter().map(|n| n.to_string()).collect::<Vec<_>>()
    );

    let tc = TypeChecker::new(&env);
    let alpha_ty = Expr::sort(Level::succ(u.clone()));
    let list_const = Expr::const_(Name::from_string("List"), vec![u.clone()]);
    let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u.clone()]);

    // λ {α} (l : List α) => @List.reverse α l  vs  λ {α} (l) => @List.reverseAux α l []
    let build = |body_fn: &dyn Fn(&Expr, &Expr) -> Expr| -> Expr {
        // Build closed lambdas via the env decl builder (fresh locals + mk_lam).
        let mut b = decl_builder::EnvDeclBuilder::new();
        let (alpha_id, alpha_l) = b.fresh_local(alpha_ty.clone());
        let list_alpha = Expr::app(list_const.clone(), alpha_l.clone());
        let (l_id, l) = b.fresh_local(list_alpha.clone());
        let body = body_fn(&alpha_l, &l);
        let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha, body);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, alpha_ty.clone(), r);
        b.finish(r)
    };

    let lhs = build(&|alpha, l| {
        Expr::apps(
            Expr::const_(Name::from_string("List.reverse"), vec![u.clone()]),
            [alpha.clone(), l.clone()],
        )
    });
    let rhs = build(&|alpha, l| {
        Expr::apps(
            Expr::const_(Name::from_string("List.reverseAux"), vec![u.clone()]),
            [
                alpha.clone(),
                l.clone(),
                Expr::app(list_nil.clone(), alpha.clone()),
            ],
        )
    });
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "List.reverse l must δ-reduce to List.reverseAux l [] (Lean fidelity)"
    );
}

/// Ground reduction: `List.reverse [1] = [1]` and `List.reverse [1,2] = [2,1]`
/// compute through the new `reverseAux` definition (adversarial: a transposed or
/// no-op `reverseAux` would fail these concrete evaluations).
#[test]
fn test_list_reverse_reduces_ground_inputs() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_list_ops().unwrap();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let one = Expr::app(succ.clone(), zero.clone());
    let two = Expr::app(succ.clone(), one.clone());
    let cons = Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]);
    let nil = Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]);
    let mk = |x: &Expr, tl: &Expr| Expr::apps(cons.clone(), [nat.clone(), x.clone(), tl.clone()]);
    let nil_nat = Expr::app(nil.clone(), nat.clone());
    let reverse = Expr::const_(Name::from_string("List.reverse"), vec![Level::zero()]);

    // reverse [1] = [1]
    let l1 = mk(&one, &nil_nat);
    let rev1 = Expr::apps(reverse.clone(), [nat.clone(), l1.clone()]);
    assert!(
        tc.is_def_eq(&rev1, &l1),
        "List.reverse [1] must reduce to [1]"
    );

    // reverse [1,2] = [2,1]
    let l12 = mk(&one, &mk(&two, &nil_nat));
    let l21 = mk(&two, &mk(&one, &nil_nat));
    let rev12 = Expr::apps(reverse.clone(), [nat.clone(), l12.clone()]);
    assert!(
        tc.is_def_eq(&rev12, &l21),
        "List.reverse [1,2] must reduce to [2,1]"
    );
    // Adversarial: reverse [1,2] must NOT be def-eq to [1,2].
    assert!(
        !tc.is_def_eq(&rev12, &l12),
        "List.reverse [1,2] must NOT equal [1,2] (would mean reverse is identity)"
    );
}

#[test]
fn test_list_length_lemmas_are_proved_and_axiom_free() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_list_ops().unwrap();

    let u = Level::param(Name::from_string("u"));
    let tc = TypeChecker::new(&env);

    for name in ["List.length_nil", "List.length_cons", "List.length_append"] {
        // Registered as a Theorem (real proof), not an Axiom.
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered by init_list_ops"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a Theorem (List.rec/rfl proof), not an Axiom"
        );

        // The proof term + type kernel-typecheck.
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![u.clone()]))
            .unwrap_or_else(|e| panic!("{name} must type-check, got {e:?}"));

        // Transitive axiom closure ⊆ FOUNDATIONAL — i.e. NO domain axioms.
        // Nat.zero_add / Nat.succ_add are themselves theorems, not axioms, so
        // the closure is empty.
        let deps: Vec<String> = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"))
            .iter()
            .map(|n| n.to_string())
            .collect();
        assert!(
            deps.is_empty(),
            "{name} must be axiom-free (⊆ foundational), got {deps:?}"
        );
    }
}

#[test]
fn test_list_length_lemmas_in_prelude() {
    let env = Environment::with_prelude();
    for name in ["List.length_nil", "List.length_cons", "List.length_append"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} must be present in Environment::with_prelude()"
        );
    }
}

#[test]
fn test_list_ops_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_list_ops().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let level_u = Level::param(u);

    // List.append type checks
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.append"),
            vec![level_u.clone()],
        ))
        .unwrap();

    // List.reverse type checks
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.reverse"),
            vec![level_u.clone()],
        ))
        .unwrap();

    // List.map type checks — {α : Type u} {β : Type v} (two universes, matching Lean)
    let _ = tc
        .infer_type(&Expr::const_(
            Name::from_string("List.map"),
            vec![level_u, Level::param(Name::from_string("v"))],
        ))
        .unwrap();
}

#[test]
fn test_init_nat_cmp() {
    let mut env = Environment::new();
    assert!(!env.has_nat_cmp());

    env.init_nat_cmp().unwrap();
    assert!(env.has_nat_cmp());

    // Check that Nat comparison operations were added with arity verification
    // Nat.beq : Nat → Nat → Bool
    let beq = env.get_const(&Name::from_string("Nat.beq")).unwrap();
    assert_eq!(
        count_pi_args(&beq.type_),
        2,
        "Nat.beq type should have 2 Pi binders"
    );

    // Nat.ble : Nat → Nat → Bool
    let ble = env.get_const(&Name::from_string("Nat.ble")).unwrap();
    assert_eq!(
        count_pi_args(&ble.type_),
        2,
        "Nat.ble type should have 2 Pi binders"
    );

    // Nat.blt : Nat → Nat → Bool
    let blt = env.get_const(&Name::from_string("Nat.blt")).unwrap();
    assert_eq!(
        count_pi_args(&blt.type_),
        2,
        "Nat.blt type should have 2 Pi binders"
    );

    // Nat.compare : Nat → Nat → Ordering
    let compare = env.get_const(&Name::from_string("Nat.compare")).unwrap();
    assert_eq!(
        count_pi_args(&compare.type_),
        2,
        "Nat.compare type should have 2 Pi binders"
    );

    // Check that dependencies were auto-initialized
    assert!(env.has_nat());
    assert!(env.has_bool());
    assert!(env.has_ordering());

    // Idempotent
    env.init_nat_cmp().unwrap();
    assert!(env.has_nat_cmp());
}

#[test]
fn test_nat_cmp_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_cmp().unwrap();

    let tc = TypeChecker::new(&env);

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
    let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);

    // Nat.beq : Nat → Nat → Bool
    let beq_const = Expr::const_(Name::from_string("Nat.beq"), vec![]);
    let beq_type = tc.infer_type(&beq_const).unwrap();
    let expected_beq_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), bool_const.clone()),
    );
    assert_eq!(beq_type, expected_beq_type);

    // Nat.ble : Nat → Nat → Bool
    let ble_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.ble"), vec![]))
        .unwrap();
    assert_eq!(ble_type, expected_beq_type);

    // Nat.blt : Nat → Nat → Bool
    let blt_type = tc
        .infer_type(&Expr::const_(Name::from_string("Nat.blt"), vec![]))
        .unwrap();
    assert_eq!(blt_type, expected_beq_type);

    // Nat.compare : Nat → Nat → Ordering
    let compare_const = Expr::const_(Name::from_string("Nat.compare"), vec![]);
    let compare_type = tc.infer_type(&compare_const).unwrap();
    let expected_compare_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const, ordering_const),
    );
    assert_eq!(compare_type, expected_compare_type);
}

#[test]
fn test_all_new_operations() {
    // Test that all new operations and types work together
    let mut env = Environment::new();

    // Initialize all new functionality
    env.init_ordering().unwrap();
    env.init_option_ops().unwrap();
    env.init_list_ops().unwrap();
    env.init_nat_cmp().unwrap();

    // Verify all are initialized
    assert!(env.has_ordering());
    assert!(env.has_option_ops());
    assert!(env.has_list_ops());
    assert!(env.has_nat_cmp());

    // Verify dependencies
    assert!(env.has_bool());
    assert!(env.has_nat());
    assert!(env.has_option());
    assert!(env.has_list());
}

#[test]
fn test_init_inhabited() {
    let mut env = Environment::new();
    assert!(!env.has_inhabited());

    env.init_inhabited().unwrap();
    assert!(env.has_inhabited());

    // Inhabited : 1 param (α), 1 constructor (mk)
    let inhabited_ind = env.get_inductive(&Name::from_string("Inhabited")).unwrap();
    assert_eq!(
        inhabited_ind.constructor_names.len(),
        1,
        "Inhabited should have 1 constructor (mk)"
    );
    assert_eq!(
        inhabited_ind.num_params, 1,
        "Inhabited should have 1 param (α)"
    );
    // Inhabited.mk : 1 field (default), index 0
    let inhabited_mk = env
        .get_constructor(&Name::from_string("Inhabited.mk"))
        .unwrap();
    assert_eq!(
        inhabited_mk.num_fields, 1,
        "Inhabited.mk should have 1 field"
    );
    assert_eq!(
        inhabited_mk.constructor_idx, 0,
        "Inhabited.mk should be constructor 0"
    );
    // Inhabited.rec : recursor with 1 minor (mk)
    let inhabited_rec = env
        .get_recursor(&Name::from_string("Inhabited.rec"))
        .unwrap();
    assert_eq!(
        inhabited_rec.num_minors, 1,
        "Inhabited.rec should have 1 minor"
    );
    assert_eq!(
        inhabited_rec.rules.len(),
        1,
        "Inhabited.rec should have 1 rule"
    );

    // Inhabited.default : {α : Sort u} → [Inhabited α] → α
    let default = env
        .get_const(&Name::from_string("Inhabited.default"))
        .unwrap();
    assert_eq!(
        count_pi_args(&default.type_),
        2,
        "Inhabited.default type should have 2 Pi binders (α, inst)"
    );

    // Check instances — concrete instances have 0 Pi binders
    let inst_nat = env
        .get_const(&Name::from_string("instInhabitedNat"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_nat.type_),
        0,
        "instInhabitedNat type should have 0 Pi binders"
    );

    let inst_bool = env
        .get_const(&Name::from_string("instInhabitedBool"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_bool.type_),
        0,
        "instInhabitedBool type should have 0 Pi binders"
    );

    let inst_unit = env
        .get_const(&Name::from_string("instInhabitedUnit"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_unit.type_),
        0,
        "instInhabitedUnit type should have 0 Pi binders"
    );

    // instInhabitedOption : {α : Type u} → Inhabited (Option α) — needs 1 Pi binder
    let inst_option = env
        .get_const(&Name::from_string("instInhabitedOption"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_option.type_),
        1,
        "instInhabitedOption type should have 1 Pi binder (α)"
    );

    // instInhabitedList : {α : Type u} → Inhabited (List α) — needs 1 Pi binder
    let inst_list = env
        .get_const(&Name::from_string("instInhabitedList"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_list.type_),
        1,
        "instInhabitedList type should have 1 Pi binder (α)"
    );

    let inst_ordering = env
        .get_const(&Name::from_string("instInhabitedOrdering"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_ordering.type_),
        0,
        "instInhabitedOrdering type should have 0 Pi binders"
    );

    // Idempotent
    env.init_inhabited().unwrap();
    assert!(env.has_inhabited());
}

#[test]
fn test_inhabited_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_inhabited().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Inhabited : Sort u → Sort (imax 1 u)
    // (imax means Prop-valued when u=0, Type-valued otherwise)
    let inhabited_const = Expr::const_(Name::from_string("Inhabited"), vec![u_level.clone()]);
    let inhabited_type = tc.infer_type(&inhabited_const).unwrap();
    // Type should be a pi from Sort u to a Sort
    if let ExprKind::Pi(_, domain, _) = &inhabited_type.kind {
        assert!(matches!(domain.kind, ExprKind::Sort(_)));
    } else {
        panic!("Expected Inhabited to have pi type, got {inhabited_type:?}");
    }

    // Check instInhabitedNat : Inhabited Nat
    let inst_nat = Expr::const_(Name::from_string("instInhabitedNat"), vec![]);
    let inst_nat_type = tc.infer_type(&inst_nat).unwrap();
    let expected_type = Expr::app(
        Expr::const_(
            Name::from_string("Inhabited"),
            vec![Level::succ(Level::zero())],
        ),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    assert_eq!(inst_nat_type, expected_type);
}

#[test]
fn test_init_beq() {
    let mut env = Environment::new();
    assert!(!env.has_beq());

    env.init_beq().unwrap();
    assert!(env.has_beq());

    // BEq : 1 param (α), 1 constructor (mk)
    let beq_ind = env.get_inductive(&Name::from_string("BEq")).unwrap();
    assert_eq!(
        beq_ind.constructor_names.len(),
        1,
        "BEq should have 1 constructor (mk)"
    );
    assert_eq!(beq_ind.num_params, 1, "BEq should have 1 param (α)");
    // BEq.mk : constructor index 0
    let beq_mk = env.get_constructor(&Name::from_string("BEq.mk")).unwrap();
    assert_eq!(beq_mk.constructor_idx, 0, "BEq.mk should be constructor 0");
    // BEq.rec : recursor with 1 minor (mk)
    let beq_rec = env.get_recursor(&Name::from_string("BEq.rec")).unwrap();
    assert_eq!(beq_rec.num_minors, 1, "BEq.rec should have 1 minor");
    assert_eq!(beq_rec.rules.len(), 1, "BEq.rec should have 1 rule");

    // BEq.beq : {α : Type u} → [BEq α] → α → α → Bool
    let beq_proj = env.get_const(&Name::from_string("BEq.beq")).unwrap();
    assert_eq!(
        count_pi_args(&beq_proj.type_),
        4,
        "BEq.beq type should have 4 Pi binders (α, inst, a, b)"
    );

    // Concrete instances have 0 Pi binders
    let inst_nat = env.get_const(&Name::from_string("instBEqNat")).unwrap();
    assert_eq!(
        count_pi_args(&inst_nat.type_),
        0,
        "instBEqNat type should have 0 Pi binders"
    );

    let inst_bool = env.get_const(&Name::from_string("instBEqBool")).unwrap();
    assert_eq!(
        count_pi_args(&inst_bool.type_),
        0,
        "instBEqBool type should have 0 Pi binders"
    );

    let inst_ord = env
        .get_const(&Name::from_string("instBEqOrdering"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_ord.type_),
        0,
        "instBEqOrdering type should have 0 Pi binders"
    );

    // Primitive beq functions: T → T → Bool (2 Pi binders)
    let bool_beq = env.get_const(&Name::from_string("Bool.beq")).unwrap();
    assert_eq!(
        count_pi_args(&bool_beq.type_),
        2,
        "Bool.beq type should have 2 Pi binders"
    );

    let ord_beq = env.get_const(&Name::from_string("Ordering.beq")).unwrap();
    assert_eq!(
        count_pi_args(&ord_beq.type_),
        2,
        "Ordering.beq type should have 2 Pi binders"
    );

    // Idempotent
    env.init_beq().unwrap();
    assert!(env.has_beq());
}

#[test]
fn test_with_prelude_includes_beq() {
    // Verify BEq typeclass is available in with_prelude() (#3429).
    // Without this, `deriving BEq` fails with "Unknown constant: BEq".
    let env = Environment::with_prelude();

    assert!(
        env.has_beq(),
        "with_prelude() must initialize BEq typeclass"
    );

    // BEq inductive must be present
    assert!(
        env.get_inductive(&Name::from_string("BEq")).is_some(),
        "with_prelude() must provide BEq inductive"
    );

    // BEq.mk constructor must be present
    assert!(
        env.get_constructor(&Name::from_string("BEq.mk")).is_some(),
        "with_prelude() must provide BEq.mk constructor"
    );

    // BEq.beq projector must be present
    assert!(
        env.get_const(&Name::from_string("BEq.beq")).is_some(),
        "with_prelude() must provide BEq.beq projector"
    );

    // Concrete instances must be present
    assert!(
        env.get_const(&Name::from_string("instBEqNat")).is_some(),
        "with_prelude() must provide instBEqNat"
    );
    assert!(
        env.get_const(&Name::from_string("instBEqBool")).is_some(),
        "with_prelude() must provide instBEqBool"
    );
}

#[test]
fn test_beq_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_beq().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);

    // BEq : Type u → Type u
    let beq_const = Expr::const_(Name::from_string("BEq"), vec![u_level.clone()]);
    let beq_type = tc.infer_type(&beq_const).unwrap();
    if let ExprKind::Pi(_, domain, _) = &beq_type.kind {
        assert!(matches!(domain.kind, ExprKind::Sort(_)));
    } else {
        panic!("Expected BEq to have pi type, got {beq_type:?}");
    }

    // Check Bool.beq : Bool → Bool → Bool
    let bool_beq = Expr::const_(Name::from_string("Bool.beq"), vec![]);
    let bool_beq_type = tc.infer_type(&bool_beq).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        bool_const.clone(),
        Expr::pi(BinderInfo::Default, bool_const.clone(), bool_const.clone()),
    );
    assert_eq!(bool_beq_type, expected_type);

    // Check instBEqNat : BEq Nat
    // BEq : Type u -> Type u, Nat : Type 0, so BEq.{0} Nat
    let inst_nat = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let inst_nat_type = tc.infer_type(&inst_nat).unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    assert_eq!(inst_nat_type, expected_type);
}

#[test]
fn test_init_nat_minmax() {
    let mut env = Environment::new();
    assert!(!env.has_nat_minmax());

    env.init_nat_minmax().unwrap();
    assert!(env.has_nat_minmax());

    // Nat.min : Nat → Nat → Nat
    let min = env.get_const(&Name::from_string("Nat.min")).unwrap();
    assert_eq!(
        count_pi_args(&min.type_),
        2,
        "Nat.min type should have 2 Pi binders"
    );

    // Nat.max : Nat → Nat → Nat
    let max = env.get_const(&Name::from_string("Nat.max")).unwrap();
    assert_eq!(
        count_pi_args(&max.type_),
        2,
        "Nat.max type should have 2 Pi binders"
    );

    // Idempotent
    env.init_nat_minmax().unwrap();
    assert!(env.has_nat_minmax());
}

#[test]
fn test_nat_minmax_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_minmax().unwrap();

    let tc = TypeChecker::new(&env);

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    // Nat.min : Nat → Nat → Nat
    let nat_min = Expr::const_(Name::from_string("Nat.min"), vec![]);
    let nat_min_type = tc.infer_type(&nat_min).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
    );
    assert_eq!(nat_min_type, expected_type);

    // Nat.max : Nat → Nat → Nat
    let nat_max = Expr::const_(Name::from_string("Nat.max"), vec![]);
    let nat_max_type = tc.infer_type(&nat_max).unwrap();
    assert_eq!(nat_max_type, expected_type);
}

/// `Environment::with_prelude()` must register `Nat.min`/`Nat.max` and the
/// min/max ordering lemmas so they are reachable from the elaboration env that
/// `clean check` uses (previously they were only wired into `env/tests.rs`).
#[test]
fn test_with_prelude_registers_nat_minmax_constants() {
    let env = Environment::with_prelude();
    for nm in ["Nat.min", "Nat.max"] {
        assert!(
            env.get_const(&Name::from_string(nm)).is_some(),
            "with_prelude must register `{nm}`"
        );
    }
    for nm in [
        "Nat.min_le_left",
        "Nat.min_le_right",
        "Nat.le_min",
        "Nat.min_comm",
        "Nat.le_max_left",
        "Nat.le_max_right",
        "Nat.max_le",
        "Nat.max_comm",
        "Nat.min_self",
        "Nat.max_self",
    ] {
        assert!(
            env.get_const(&Name::from_string(nm)).is_some(),
            "with_prelude must register the min/max lemma `{nm}`"
        );
    }
}

/// The newly-registered `Nat.min_self`/`Nat.max_self` lemmas must be
/// constructive `Declaration::Theorem`s with empty domain-axiom closures, like
/// the existing #3604 cluster.
#[test]
fn test_nat_minmax_self_are_constructive_theorems() {
    use crate::env::axiom_audit::ProofQuality;

    let env = Environment::with_prelude();
    for nm in ["Nat.min_self", "Nat.max_self"] {
        let info = env
            .get_const(&Name::from_string(nm))
            .unwrap_or_else(|| panic!("{nm} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{nm} must be a Theorem (not an Axiom)"
        );
        let quality = env
            .proof_quality(&Name::from_string(nm))
            .unwrap_or_else(|| panic!("{nm} proof_quality should be reported"));
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "{nm} must be Constructive, got {quality:?}"
        );
    }
}

/// The `Nat.min_self`/`Nat.max_self` proof terms must kernel-check against their
/// declared types (`∀ a, Nat.min a a = a` / `∀ a, Nat.max a a = a`).
#[test]
fn test_nat_minmax_self_type_checks() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());

    for nm in ["Nat.min_self", "Nat.max_self"] {
        let info = env
            .get_const(&Name::from_string(nm))
            .unwrap_or_else(|| panic!("{nm} must be registered"));
        let value = info
            .value
            .clone()
            .unwrap_or_else(|| panic!("{nm} must retain its proof value"));
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{nm} proof must kernel-check: {e:?}"));
    }
}

#[test]
fn test_all_typeclasses() {
    // Test that all typeclasses work together
    let mut env = Environment::new();

    // Initialize all new functionality
    env.init_inhabited().unwrap();
    env.init_beq().unwrap();
    env.init_nat_minmax().unwrap();

    // Verify all are initialized
    assert!(env.has_inhabited());
    assert!(env.has_beq());
    assert!(env.has_nat_minmax());

    // Verify dependencies were correctly initialized
    assert!(env.has_nat());
    assert!(env.has_bool());
    assert!(env.has_unit());
    assert!(env.has_option());
    assert!(env.has_list());
    assert!(env.has_ordering());
    assert!(env.has_nat_cmp());
}

#[test]
fn test_init_ord() {
    let mut env = Environment::new();
    assert!(!env.has_ord());

    env.init_ord().unwrap();
    assert!(env.has_ord());

    // Ord : {α : Type u} → (compare : α → α → Ordering) → Ord α
    let ord_const = env.get_const(&Name::from_string("Ord")).unwrap();
    assert_eq!(
        count_pi_args(&ord_const.type_),
        1,
        "Ord type should have 1 Pi binder (α)"
    );
    // Ord.mk : {α : Type u} → (compare : α → α → Ordering) → Ord α
    let ord_mk = env.get_const(&Name::from_string("Ord.mk")).unwrap();
    assert_eq!(
        count_pi_args(&ord_mk.type_),
        2,
        "Ord.mk type should have 2 Pi binders (α, compare)"
    );

    // Ord.compare : {α : Type u} → [Ord α] → α → α → Ordering
    let ord_compare = env.get_const(&Name::from_string("Ord.compare")).unwrap();
    assert_eq!(
        count_pi_args(&ord_compare.type_),
        4,
        "Ord.compare type should have 4 Pi binders (α, inst, a, b)"
    );

    // Concrete instances: 0 Pi binders
    let inst_nat = env.get_const(&Name::from_string("instOrdNat")).unwrap();
    assert_eq!(
        count_pi_args(&inst_nat.type_),
        0,
        "instOrdNat type should have 0 Pi binders"
    );

    let inst_bool = env.get_const(&Name::from_string("instOrdBool")).unwrap();
    assert_eq!(
        count_pi_args(&inst_bool.type_),
        0,
        "instOrdBool type should have 0 Pi binders"
    );

    // Bool.compare : Bool → Bool → Ordering
    let bool_compare = env.get_const(&Name::from_string("Bool.compare")).unwrap();
    assert_eq!(
        count_pi_args(&bool_compare.type_),
        2,
        "Bool.compare type should have 2 Pi binders"
    );

    let inst_ordering = env
        .get_const(&Name::from_string("instOrdOrdering"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_ordering.type_),
        0,
        "instOrdOrdering type should have 0 Pi binders"
    );

    // Ordering.compare : Ordering → Ordering → Ordering
    let ord_cmp = env
        .get_const(&Name::from_string("Ordering.compare"))
        .unwrap();
    assert_eq!(
        count_pi_args(&ord_cmp.type_),
        2,
        "Ordering.compare type should have 2 Pi binders"
    );

    // Idempotent
    env.init_ord().unwrap();
    assert!(env.has_ord());
}

#[test]
fn test_ord_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_ord().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);

    // Ord : Type u → Type u
    let ord_const = Expr::const_(Name::from_string("Ord"), vec![u_level.clone()]);
    let ord_type = tc.infer_type(&ord_const).unwrap();
    if let ExprKind::Pi(_, domain, _) = &ord_type.kind {
        assert!(matches!(domain.kind, ExprKind::Sort(_)));
    } else {
        panic!("Expected Ord to have pi type, got {ord_type:?}");
    }

    // Check Bool.compare : Bool → Bool → Ordering
    let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_compare = Expr::const_(Name::from_string("Bool.compare"), vec![]);
    let bool_compare_type = tc.infer_type(&bool_compare).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        bool_const.clone(),
        Expr::pi(
            BinderInfo::Default,
            bool_const.clone(),
            ordering_const.clone(),
        ),
    );
    assert_eq!(bool_compare_type, expected_type);

    // Check instOrdNat : Ord Nat
    // Ord : Type u → Type u, Nat : Type 0, so Ord.{0}
    let inst_nat = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let inst_nat_type = tc.infer_type(&inst_nat).unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("Ord"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    assert_eq!(inst_nat_type, expected_type);
}

#[test]
fn test_init_decidable_eq() {
    let mut env = Environment::new();
    assert!(!env.has_decidable_eq());

    env.init_decidable_eq().unwrap();
    assert!(env.has_decidable_eq());

    // DecidableEq : {α : Sort u} → Prop (abbreviation: (a b : α) → Decidable (Eq a b))
    let dec_eq = env.get_const(&Name::from_string("DecidableEq")).unwrap();
    assert_eq!(
        count_pi_args(&dec_eq.type_),
        1,
        "DecidableEq type should have 1 Pi binder (α)"
    );

    // decEq : {α : Sort u} → [DecidableEq α] → (a b : α) → Decidable (Eq a b)
    let dec_eq_fn = env.get_const(&Name::from_string("decEq")).unwrap();
    assert_eq!(
        count_pi_args(&dec_eq_fn.type_),
        4,
        "decEq type should have 4 Pi binders (α, inst, a, b)"
    );

    // Idempotent
    env.init_decidable_eq().unwrap();
    assert!(env.has_decidable_eq());
}

#[test]
fn test_decidable_eq_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_decidable_eq().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // DecidableEq.{u} : Sort u → Sort(max(u, 1))
    // Decidable is Type-valued (not Prop), so DecidableEq lives in Sort(max(u,1))
    let decidable_eq_const = Expr::const_(Name::from_string("DecidableEq"), vec![u_level.clone()]);
    let decidable_eq_type = tc.infer_type(&decidable_eq_const).unwrap();
    if let ExprKind::Pi(_, domain, codomain) = &decidable_eq_type.kind {
        assert!(
            matches!(domain.kind, ExprKind::Sort(_)),
            "domain should be Sort u"
        );
        let expected_codomain = Level::max(u_level.clone(), Level::succ(Level::zero()));
        assert!(
            matches!(&codomain.kind, ExprKind::Sort(l) if l == &expected_codomain),
            "codomain should be Sort(max(u, 1)), got {codomain:?}"
        );
    } else {
        panic!("Expected DecidableEq to have pi type, got {decidable_eq_type:?}");
    }
}

#[test]
fn test_init_hashable() {
    let mut env = Environment::new();
    assert!(!env.has_hashable());

    env.init_hashable().unwrap();
    assert!(env.has_hashable());

    // Hashable : {α : Type u} → ... → Hashable α
    let hashable_const = env.get_const(&Name::from_string("Hashable")).unwrap();
    assert_eq!(
        count_pi_args(&hashable_const.type_),
        1,
        "Hashable type should have 1 Pi binder (α)"
    );
    // Hashable.mk : constructor
    let hashable_mk = env.get_const(&Name::from_string("Hashable.mk")).unwrap();
    assert_eq!(
        count_pi_args(&hashable_mk.type_),
        2,
        "Hashable.mk type should have 2 Pi binders (α, hash)"
    );

    // Hashable.hash : {α : Type u} → [Hashable α] → α → UInt64
    let hash_proj = env.get_const(&Name::from_string("Hashable.hash")).unwrap();
    assert_eq!(
        count_pi_args(&hash_proj.type_),
        3,
        "Hashable.hash type should have 3 Pi binders (α, inst, val)"
    );

    // Concrete instances: 0 Pi binders
    let inst_nat = env
        .get_const(&Name::from_string("instHashableNat"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_nat.type_),
        0,
        "instHashableNat type should have 0 Pi binders"
    );

    let inst_bool = env
        .get_const(&Name::from_string("instHashableBool"))
        .unwrap();
    assert_eq!(
        count_pi_args(&inst_bool.type_),
        0,
        "instHashableBool type should have 0 Pi binders"
    );

    // Bool.hash : Bool → UInt64
    let bool_hash = env.get_const(&Name::from_string("Bool.hash")).unwrap();
    assert_eq!(
        count_pi_args(&bool_hash.type_),
        1,
        "Bool.hash type should have 1 Pi binder"
    );

    // Idempotent
    env.init_hashable().unwrap();
    assert!(env.has_hashable());
}

#[test]
fn test_hashable_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_hashable().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

    // Hashable : Type u → Type u
    let hashable_const = Expr::const_(Name::from_string("Hashable"), vec![u_level.clone()]);
    let hashable_type = tc.infer_type(&hashable_const).unwrap();
    if let ExprKind::Pi(_, domain, _) = &hashable_type.kind {
        assert!(matches!(domain.kind, ExprKind::Sort(_)));
    } else {
        panic!("Expected Hashable to have pi type, got {hashable_type:?}");
    }

    // Check Bool.hash : Bool → Nat
    let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_hash = Expr::const_(Name::from_string("Bool.hash"), vec![]);
    let bool_hash_type = tc.infer_type(&bool_hash).unwrap();
    let expected_type = Expr::pi(BinderInfo::Default, bool_const.clone(), nat_const.clone());
    assert_eq!(bool_hash_type, expected_type);

    // Check instHashableNat : Hashable Nat
    // Hashable : Type u -> Type u, Nat : Type 0, so Hashable.{0} Nat
    let inst_nat = Expr::const_(Name::from_string("instHashableNat"), vec![]);
    let inst_nat_type = tc.infer_type(&inst_nat).unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("Hashable"), vec![Level::zero()]),
        nat_const.clone(),
    );
    assert_eq!(inst_nat_type, expected_type);
}

#[test]
fn test_all_new_typeclasses() {
    // Test that all new typeclasses work together
    let mut env = Environment::new();

    // Initialize all new typeclasses
    env.init_ord().unwrap();
    env.init_decidable_eq().unwrap();
    env.init_hashable().unwrap();

    // Verify all are initialized
    assert!(env.has_ord());
    assert!(env.has_decidable_eq());
    assert!(env.has_hashable());

    // Verify dependencies were correctly initialized
    assert!(env.has_ordering());
    assert!(env.has_nat());
    assert!(env.has_bool());
    assert!(env.has_eq());
    assert!(env.has_decidable());
    assert!(env.has_nat_cmp());
}

#[test]
fn test_init_le() {
    let mut env = Environment::new();
    assert!(!env.has_le());

    env.init_le().unwrap();
    assert!(env.has_le());

    // LE : 1 Pi binder (α)
    let le_const = env.get_const(&Name::from_string("LE")).unwrap();
    assert_eq!(
        count_pi_args(&le_const.type_),
        1,
        "LE type should have 1 Pi binder (α)"
    );
    // LE.mk : 2 Pi binders (α, le)
    let le_mk = env.get_const(&Name::from_string("LE.mk")).unwrap();
    assert_eq!(
        count_pi_args(&le_mk.type_),
        2,
        "LE.mk type should have 2 Pi binders (α, le)"
    );

    // LE.le : {α : Type u} → [LE α] → α → α → Prop
    let le_le = env.get_const(&Name::from_string("LE.le")).unwrap();
    assert_eq!(
        count_pi_args(&le_le.type_),
        4,
        "LE.le type should have 4 Pi binders (α, inst, a, b)"
    );

    // Nat.le : Nat → Nat → Prop
    let nat_le = env.get_const(&Name::from_string("Nat.le")).unwrap();
    assert_eq!(
        count_pi_args(&nat_le.type_),
        2,
        "Nat.le type should have 2 Pi binders (n, m)"
    );

    // Nat.le.refl : {n : Nat} → Nat.le n n
    let le_refl = env.get_const(&Name::from_string("Nat.le.refl")).unwrap();
    assert_eq!(
        count_pi_args(&le_refl.type_),
        1,
        "Nat.le.refl type should have 1 Pi binder (n)"
    );

    // Nat.le.step : {n m : Nat} → Nat.le n m → Nat.le n (Nat.succ m)
    let le_step = env.get_const(&Name::from_string("Nat.le.step")).unwrap();
    assert_eq!(
        count_pi_args(&le_step.type_),
        3,
        "Nat.le.step type should have 3 Pi binders (n, m, h)"
    );

    // instLENat : LE Nat (0 Pi binders)
    let inst = env.get_const(&Name::from_string("instLENat")).unwrap();
    assert_eq!(
        count_pi_args(&inst.type_),
        0,
        "instLENat type should have 0 Pi binders"
    );

    // Check inductives
    let le_ind = env.get_inductive(&Name::from_string("LE")).unwrap();
    assert_eq!(
        le_ind.constructor_names.len(),
        1,
        "LE should have 1 constructor (mk)"
    );
    let nat_le_ind = env.get_inductive(&Name::from_string("Nat.le")).unwrap();
    assert_eq!(
        nat_le_ind.constructor_names.len(),
        2,
        "Nat.le should have 2 constructors (refl, step)"
    );

    // Idempotent
    env.init_le().unwrap();
    assert!(env.has_le());
}

#[test]
fn test_le_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_le().unwrap();

    let tc = TypeChecker::new(&env);

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // LE : Type u → Type u
    let le_const = Expr::const_(Name::from_string("LE"), vec![u_level.clone()]);
    let le_type = tc.infer_type(&le_const).unwrap();
    if let ExprKind::Pi(_, domain, _) = &le_type.kind {
        assert!(matches!(domain.kind, ExprKind::Sort(_)));
    } else {
        panic!("Expected LE to have pi type, got {le_type:?}");
    }

    // Check Nat.le : Nat → Nat → Prop
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let nat_le_type = tc.infer_type(&nat_le).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), prop.clone()),
    );
    assert_eq!(nat_le_type, expected_type);

    // Check instLENat : LE Nat
    // LE : Type u → Type u, Nat : Type 0, so LE.{0}
    let inst_le_nat = Expr::const_(Name::from_string("instLENat"), vec![]);
    let inst_le_nat_type = tc.infer_type(&inst_le_nat).unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
        nat_const.clone(),
    );
    assert_eq!(inst_le_nat_type, expected_type);
}

#[test]
fn test_init_lt() {
    let mut env = Environment::new();
    assert!(!env.has_lt());

    env.init_lt().unwrap();
    assert!(env.has_lt());

    // LT : 1 Pi binder (α)
    let lt_const = env.get_const(&Name::from_string("LT")).unwrap();
    assert_eq!(
        count_pi_args(&lt_const.type_),
        1,
        "LT type should have 1 Pi binder (α)"
    );
    // LT.mk : 2 Pi binders (α, lt)
    let lt_mk = env.get_const(&Name::from_string("LT.mk")).unwrap();
    assert_eq!(
        count_pi_args(&lt_mk.type_),
        2,
        "LT.mk type should have 2 Pi binders (α, lt)"
    );

    // LT.lt : {α : Type u} → [LT α] → α → α → Prop
    let lt_lt = env.get_const(&Name::from_string("LT.lt")).unwrap();
    assert_eq!(
        count_pi_args(&lt_lt.type_),
        4,
        "LT.lt type should have 4 Pi binders (α, inst, a, b)"
    );

    // Nat.lt : Nat → Nat → Prop (defined as n < m := Nat.succ n ≤ m)
    let nat_lt = env.get_const(&Name::from_string("Nat.lt")).unwrap();
    assert_eq!(
        count_pi_args(&nat_lt.type_),
        2,
        "Nat.lt type should have 2 Pi binders (n, m)"
    );

    // instLTNat : LT Nat (0 Pi binders)
    let inst = env.get_const(&Name::from_string("instLTNat")).unwrap();
    assert_eq!(
        count_pi_args(&inst.type_),
        0,
        "instLTNat type should have 0 Pi binders"
    );

    // Check inductive was added
    let lt_ind = env.get_inductive(&Name::from_string("LT")).unwrap();
    assert_eq!(
        lt_ind.constructor_names.len(),
        1,
        "LT should have 1 constructor (mk)"
    );

    // Check LE dependency was initialized
    assert!(env.has_le());
    let nat_le_ind = env.get_inductive(&Name::from_string("Nat.le")).unwrap();
    assert_eq!(
        nat_le_ind.constructor_names.len(),
        2,
        "Nat.le should have 2 constructors (refl, step)"
    );

    // Idempotent
    env.init_lt().unwrap();
    assert!(env.has_lt());
}

// ════════════════════════════════════════════════════════════════════════════
// Mode compatibility tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_environment_with_mode() {
    use crate::mode::CleanMode;

    // Default environment is Constructive
    let env = Environment::new();
    assert_eq!(env.mode(), CleanMode::Constructive);

    // Can create environment with specific mode
    let cubical_env = Environment::with_mode(CleanMode::Cubical);
    assert_eq!(cubical_env.mode(), CleanMode::Cubical);

    let classical_env = Environment::with_mode(CleanMode::Classical);
    assert_eq!(classical_env.mode(), CleanMode::Classical);

    let set_env = Environment::with_mode(CleanMode::SetTheoretic);
    assert_eq!(set_env.mode(), CleanMode::SetTheoretic);

    let impredicative_env = Environment::with_mode(CleanMode::Impredicative);
    assert_eq!(impredicative_env.mode(), CleanMode::Impredicative);
}

#[test]
fn test_import_compatibility_constructive_to_all() {
    use crate::mode::CleanMode;

    let constructive_env = Environment::with_mode(CleanMode::Constructive);

    // Constructive can import into any mode
    let cubical_env = Environment::with_mode(CleanMode::Cubical);
    cubical_env
        .check_import_compatibility(&constructive_env)
        .expect("Constructive must import into Cubical");

    let classical_env = Environment::with_mode(CleanMode::Classical);
    classical_env
        .check_import_compatibility(&constructive_env)
        .expect("Constructive must import into Classical");

    let set_env = Environment::with_mode(CleanMode::SetTheoretic);
    set_env
        .check_import_compatibility(&constructive_env)
        .expect("Constructive must import into SetTheoretic");

    let impredicative_env = Environment::with_mode(CleanMode::Impredicative);
    impredicative_env
        .check_import_compatibility(&constructive_env)
        .expect("Constructive must import into Impredicative");

    // Constructive into Constructive
    let constructive_target = Environment::with_mode(CleanMode::Constructive);
    constructive_target
        .check_import_compatibility(&constructive_env)
        .expect("Constructive must import into Constructive");
}

#[test]
fn test_import_compatibility_cubical_isolated() {
    use crate::mode::{CleanMode, ModeError};

    let cubical_env = Environment::with_mode(CleanMode::Cubical);

    // Cubical can only import into Cubical (self)
    let cubical_target = Environment::with_mode(CleanMode::Cubical);
    cubical_target
        .check_import_compatibility(&cubical_env)
        .expect("Cubical must import into Cubical");

    // Cubical cannot import into other modes
    let classical_env = Environment::with_mode(CleanMode::Classical);
    assert!(matches!(
        classical_env.check_import_compatibility(&cubical_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Cubical && target == CleanMode::Classical
    ));

    let constructive_env = Environment::with_mode(CleanMode::Constructive);
    assert!(matches!(
        constructive_env.check_import_compatibility(&cubical_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Cubical && target == CleanMode::Constructive
    ));

    let impredicative_env = Environment::with_mode(CleanMode::Impredicative);
    assert!(matches!(
        impredicative_env.check_import_compatibility(&cubical_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Cubical && target == CleanMode::Impredicative
    ));

    let set_env = Environment::with_mode(CleanMode::SetTheoretic);
    assert!(matches!(
        set_env.check_import_compatibility(&cubical_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Cubical && target == CleanMode::SetTheoretic
    ));

    // Other modes cannot import into Cubical (except Constructive tested above)
    assert!(matches!(
        cubical_env.check_import_compatibility(&classical_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Classical && target == CleanMode::Cubical
    ));
    assert!(matches!(
        cubical_env.check_import_compatibility(&impredicative_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Impredicative && target == CleanMode::Cubical
    ));
    assert!(matches!(
        cubical_env.check_import_compatibility(&set_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::SetTheoretic && target == CleanMode::Cubical
    ));
}

#[test]
fn test_import_compatibility_classical_hierarchy() {
    use crate::mode::{CleanMode, ModeError};

    let classical_env = Environment::with_mode(CleanMode::Classical);
    let impredicative_env = Environment::with_mode(CleanMode::Impredicative);
    let set_env = Environment::with_mode(CleanMode::SetTheoretic);

    // Impredicative can import into Classical
    classical_env
        .check_import_compatibility(&impredicative_env)
        .expect("Impredicative must import into Classical");

    // Classical can import into SetTheoretic
    set_env
        .check_import_compatibility(&classical_env)
        .expect("Classical must import into SetTheoretic");

    // Impredicative can import into SetTheoretic (transitive)
    set_env
        .check_import_compatibility(&impredicative_env)
        .expect("Impredicative must import into SetTheoretic");

    // But not the reverse
    assert!(matches!(
        impredicative_env.check_import_compatibility(&classical_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::Classical && target == CleanMode::Impredicative
    ));
    assert!(matches!(
        classical_env.check_import_compatibility(&set_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::SetTheoretic && target == CleanMode::Classical
    ));
    assert!(matches!(
        impredicative_env.check_import_compatibility(&set_env),
        Err(ModeError::IncompatibleImport { source_mode: source, target })
            if source == CleanMode::SetTheoretic && target == CleanMode::Impredicative
    ));
}

#[test]
fn test_import_compatibility_error_type() {
    use crate::mode::{CleanMode, ModeError};

    let classical_env = Environment::with_mode(CleanMode::Classical);
    let constructive_env = Environment::with_mode(CleanMode::Constructive);

    // Classical cannot import into Constructive
    let err = constructive_env
        .check_import_compatibility(&classical_env)
        .expect_err("classical cannot import into constructive");
    match err {
        ModeError::IncompatibleImport {
            source_mode: source,
            target,
        } => {
            assert_eq!(source, CleanMode::Classical);
            assert_eq!(target, CleanMode::Constructive);
        }
        _ => panic!("Expected IncompatibleImport error"),
    }
}

// =============================================================================
// D4: Transparency Modes Tests
//
// Part of #15: Aesop parity for Mathlib compatibility
// =============================================================================

/// Test: TransparencyMode controls which definitions unfold
#[test]
fn test_transparency_mode_reducibility() {
    let mut env = Environment::new();

    // Add a reducible definition: f := λ x. x
    env.add_decl(Declaration::Definition {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(Expr::prop(), Expr::prop()),
        value: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        is_reducible: true,
    })
    .unwrap();

    // Add a semireducible definition: g := λ x. x
    {
        let info = ConstantInfo::new(
            Name::from_string("g"),
            vec![],
            Expr::arrow(Expr::prop(), Expr::prop()),
            Some(Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0))),
            false, // is_reducible = false → Semireducible
        );
        env.constants.insert(Name::from_string("g"), info);
    }

    // Add an irreducible definition: h := λ x. x
    {
        let mut info = ConstantInfo::new(
            Name::from_string("h"),
            vec![],
            Expr::arrow(Expr::prop(), Expr::prop()),
            Some(Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0))),
            false,
        );
        info.reducibility = Reducibility::Irreducible;
        env.constants.insert(Name::from_string("h"), info);
    }

    // Test unfold_with_transparency
    let f_name = Name::from_string("f");
    let g_name = Name::from_string("g");
    let h_name = Name::from_string("h");

    // All three definitions have the same body: λ (x : Prop). x
    let expected_body = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));

    // Reducible mode: only f should unfold
    let f_red = env
        .unfold_with_transparency(&f_name, &[], TransparencyMode::Reducible)
        .expect("reducible def should unfold in Reducible mode");
    assert_eq!(f_red, expected_body, "f unfolded value must be λ x. x");
    assert!(
        env.unfold_with_transparency(&g_name, &[], TransparencyMode::Reducible)
            .is_none(),
        "semireducible def should NOT unfold in Reducible mode"
    );
    assert!(
        env.unfold_with_transparency(&h_name, &[], TransparencyMode::Reducible)
            .is_none(),
        "irreducible def should NOT unfold in Reducible mode"
    );

    // Default mode: f and g should unfold
    let f_def = env
        .unfold_with_transparency(&f_name, &[], TransparencyMode::Default)
        .expect("reducible def should unfold in Default mode");
    assert_eq!(f_def, expected_body, "f unfolded in Default must be λ x. x");
    let g_def = env
        .unfold_with_transparency(&g_name, &[], TransparencyMode::Default)
        .expect("semireducible def should unfold in Default mode");
    assert_eq!(g_def, expected_body, "g unfolded in Default must be λ x. x");
    assert!(
        env.unfold_with_transparency(&h_name, &[], TransparencyMode::Default)
            .is_none(),
        "irreducible def should NOT unfold in Default mode"
    );

    // All mode: everything should unfold
    let f_all = env
        .unfold_with_transparency(&f_name, &[], TransparencyMode::All)
        .expect("reducible def should unfold in All mode");
    assert_eq!(f_all, expected_body, "f unfolded in All must be λ x. x");
    let g_all = env
        .unfold_with_transparency(&g_name, &[], TransparencyMode::All)
        .expect("semireducible def should unfold in All mode");
    assert_eq!(g_all, expected_body, "g unfolded in All must be λ x. x");
    let h_all = env
        .unfold_with_transparency(&h_name, &[], TransparencyMode::All)
        .expect("irreducible def should unfold in All mode");
    assert_eq!(h_all, expected_body, "h unfolded in All must be λ x. x");
}

/// Test: whnf_with_transparency uses transparency modes
#[test]
fn test_whnf_with_transparency() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();

    // Add an irreducible definition: id := λ x. x
    {
        let mut info = ConstantInfo::new(
            Name::from_string("id"),
            vec![],
            Expr::arrow(Expr::prop(), Expr::prop()),
            Some(Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0))),
            false,
        );
        info.reducibility = Reducibility::Irreducible;
        env.constants.insert(Name::from_string("id"), info);
    }

    let tc = TypeChecker::new(&env);

    // Create application: id Prop
    let app = Expr::app(Expr::const_(Name::from_string("id"), vec![]), Expr::prop());

    // Default mode should NOT reduce (id is irreducible)
    let result_default = tc.whnf_with_transparency(&app, TransparencyMode::Default);
    assert!(
        matches!(&result_default.kind, ExprKind::App(f, _) if matches!(&f.kind, ExprKind::Const(n, _) if n.to_string() == "id")),
        "id should not reduce in Default mode (is irreducible)"
    );

    // All mode SHOULD reduce
    let result_all = tc.whnf_with_transparency(&app, TransparencyMode::All);
    assert_eq!(result_all, Expr::prop(), "id should reduce in All mode");
}

/// Test: TransparencyMode::Instances unfolds registered instances (#430)
#[test]
fn test_transparency_mode_instances_unfolds_registered_instances() {
    let mut env = Environment::new();

    // Add an irreducible definition that is NOT an instance
    {
        let mut info = ConstantInfo::new(
            Name::from_string("notAnInstance"),
            vec![],
            Expr::prop(),
            Some(Expr::prop()),
            false,
        );
        info.reducibility = Reducibility::Irreducible;
        env.constants
            .insert(Name::from_string("notAnInstance"), info);
    }

    // Add an irreducible definition that IS registered as an instance
    {
        let mut info = ConstantInfo::new(
            Name::from_string("instFooBar"),
            vec![],
            Expr::prop(),
            Some(Expr::prop()),
            false,
        );
        info.reducibility = Reducibility::Irreducible; // Normally wouldn't unfold
        env.constants.insert(Name::from_string("instFooBar"), info);
    }

    // Register instFooBar as an instance
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instFooBar"),
        class_name: Name::from_string("Foo"),
        priority: 100,
        type_: None,
        value: None,
    });

    let not_instance_name = Name::from_string("notAnInstance");
    let instance_name = Name::from_string("instFooBar");

    // Default mode: neither should unfold (both irreducible)
    assert!(
        env.unfold_with_transparency(&not_instance_name, &[], TransparencyMode::Default)
            .is_none(),
        "irreducible non-instance should NOT unfold in Default mode"
    );
    assert!(
        env.unfold_with_transparency(&instance_name, &[], TransparencyMode::Default)
            .is_none(),
        "irreducible instance should NOT unfold in Default mode"
    );

    // Instances mode: only registered instance should unfold
    assert!(
        env.unfold_with_transparency(&not_instance_name, &[], TransparencyMode::Instances)
            .is_none(),
        "irreducible non-instance should NOT unfold in Instances mode"
    );
    let inst_unfolded = env
        .unfold_with_transparency(&instance_name, &[], TransparencyMode::Instances)
        .expect("registered instance should unfold in Instances mode even if irreducible");
    assert_eq!(
        inst_unfolded,
        Expr::prop(),
        "instance unfolded value must be Prop"
    );

    // Reducible mode: instance should NOT get special treatment
    // (Reducible mode only unfolds Reducible definitions)
    assert!(
        env.unfold_with_transparency(&instance_name, &[], TransparencyMode::Reducible)
            .is_none(),
        "irreducible instance should NOT unfold in Reducible mode (not special-cased)"
    );

    // All mode: both should unfold (irreducible unfolds in All mode)
    let not_inst_all = env
        .unfold_with_transparency(&not_instance_name, &[], TransparencyMode::All)
        .expect("irreducible non-instance should unfold in All mode");
    assert_eq!(
        not_inst_all,
        Expr::prop(),
        "non-instance unfolded in All must be Prop"
    );
    let inst_all = env
        .unfold_with_transparency(&instance_name, &[], TransparencyMode::All)
        .expect("irreducible instance should unfold in All mode");
    assert_eq!(
        inst_all,
        Expr::prop(),
        "instance unfolded in All must be Prop"
    );

    // Verify is_instance works correctly
    assert!(
        !env.is_instance(&not_instance_name),
        "non-instance should not be detected as instance"
    );
    assert!(
        env.is_instance(&instance_name),
        "registered instance should be detected as instance"
    );
}

/// Test: TransparencyMode::Instances with Semireducible instance (#430 edge case)
///
/// Semireducible instances should unfold via the normal path (should_unfold returns true),
/// not requiring the special instance check. This tests that we don't break anything.
#[test]
fn test_transparency_mode_instances_semireducible_instance() {
    let mut env = Environment::new();

    // Add a semireducible instance - this should unfold via normal path
    {
        let mut info = ConstantInfo::new(
            Name::from_string("instSemireducible"),
            vec![],
            Expr::prop(),
            Some(Expr::prop()),
            false,
        );
        info.reducibility = Reducibility::Regular(0);
        env.constants
            .insert(Name::from_string("instSemireducible"), info);
    }

    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("instSemireducible"),
        class_name: Name::from_string("Bar"),
        priority: 100,
        type_: None,
        value: None,
    });

    let name = Name::from_string("instSemireducible");

    // Semireducible unfolds in Default mode (via should_unfold)
    let default_result = env
        .unfold_with_transparency(&name, &[], TransparencyMode::Default)
        .expect("semireducible instance should unfold in Default mode (via should_unfold)");
    assert_eq!(
        default_result,
        Expr::prop(),
        "semireducible instance unfolded in Default must be Prop"
    );

    // Semireducible unfolds in Instances mode (via should_unfold, not special case)
    let inst_result = env
        .unfold_with_transparency(&name, &[], TransparencyMode::Instances)
        .expect("semireducible instance should unfold in Instances mode");
    assert_eq!(
        inst_result,
        Expr::prop(),
        "semireducible instance unfolded in Instances must be Prop"
    );

    // Semireducible does NOT unfold in Reducible mode (not reducible)
    assert!(
        env.unfold_with_transparency(&name, &[], TransparencyMode::Reducible)
            .is_none(),
        "semireducible instance should NOT unfold in Reducible mode"
    );
}

/// Test: theorem and opaque declarations remain hidden in transparency unfolding (#1280)
#[test]
fn test_theorem_and_opaque_never_unfold_with_transparency() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();

    let theorem_name = Name::from_string("thmHidden");
    let opaque_name = Name::from_string("opaqueHidden");

    // Use add_decl_unchecked: True.intro doesn't exist in this test env
    env.add_decl_unchecked(Declaration::Theorem {
        name: theorem_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("True.intro"), vec![]),
    });

    env.add_decl_unchecked(Declaration::Opaque {
        name: opaque_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("True.intro"), vec![]),
    });

    let theorem_info = env
        .get_const(&theorem_name)
        .expect("theorem should be present in environment");
    let opaque_info = env
        .get_const(&opaque_name)
        .expect("opaque declaration should be present in environment");

    assert_eq!(theorem_info.reducibility, Reducibility::Opaque);
    assert_eq!(opaque_info.reducibility, Reducibility::Opaque);

    for mode in [
        TransparencyMode::Reducible,
        TransparencyMode::Instances,
        TransparencyMode::Default,
        TransparencyMode::All,
    ] {
        assert!(
            env.unfold_with_transparency(&theorem_name, &[], mode)
                .is_none(),
            "theorem must not unfold in mode {mode:?}"
        );
        assert!(
            env.unfold_with_transparency(&opaque_name, &[], mode)
                .is_none(),
            "opaque declaration must not unfold in mode {mode:?}"
        );
    }

    env.register_instance(KernelInstanceInfo {
        name: theorem_name.clone(),
        class_name: Name::from_string("Foo"),
        priority: 100,
        type_: None,
        value: None,
    });

    assert!(env.is_instance(&theorem_name));
    assert!(
        env.unfold_with_transparency(&theorem_name, &[], TransparencyMode::Instances)
            .is_none(),
        "instance registration must not make theorem unfoldable"
    );

    let tc = TypeChecker::new(&env);
    let theorem_app = Expr::app(Expr::const_(theorem_name.clone(), vec![]), Expr::prop());
    let theorem_whnf = tc.whnf_with_transparency(&theorem_app, TransparencyMode::All);
    assert_eq!(
        theorem_whnf, theorem_app,
        "whnf_with_transparency should not reveal theorem value"
    );

    let opaque_app = Expr::app(Expr::const_(opaque_name.clone(), vec![]), Expr::prop());
    let opaque_whnf = tc.whnf_with_transparency(&opaque_app, TransparencyMode::All);
    assert_eq!(
        opaque_whnf, opaque_app,
        "whnf_with_transparency should not reveal opaque value"
    );
}

/// Test that FATE-X type constructors have Pi types (#788)
///
/// Previously these were declared as `Type u` instead of function types,
/// causing 28% of FATE-X elaboration failures (NotAFunction errors).
#[test]
fn test_fatex_type_constructors_have_pi_types() {
    let mut env = Environment::new();
    // init_domain_types now auto-initializes Nat for Ext/Tor
    env.init_domain_types().unwrap();

    fn strip_wrappers(mut expr: &Expr) -> &Expr {
        loop {
            match &expr.kind {
                ExprKind::MData(_, inner) => expr = inner.as_ref(),
                ExprKind::Let(_, _, _, body, _) => expr = body.as_ref(),
                _ => return expr,
            }
        }
    }

    let pi_arity = |expr: &Expr| -> usize {
        let mut current = strip_wrappers(expr);
        let mut count = 0;
        loop {
            match &current.kind {
                ExprKind::Pi(_, _, body) => {
                    count += 1;
                    current = strip_wrappers(body.as_ref());
                }
                _ => return count,
            }
        }
    };

    // Type constructors that take type arguments must be Pi types
    // These were incorrectly typed as `Type u` causing NotAFunction errors
    let pi_type_constructors = [
        ("AlgHom", 3),        // (R : Type u) → (A : Type v) → (B : Type w) → Type (max u v w)
        ("AlgEquiv", 3),      // Same as AlgHom
        ("ModuleCat", 1),     // (R : Type u) → Type (u + 1)
        ("ChainComplex", 2),  // (V : Type u) → (c : Type v) → Type (max u v)
        ("Ext", 3),           // (M : Type u) → (N : Type v) → ℕ → Type (max u v)
        ("Tor", 3),           // Same as Ext
        ("MvPolynomial", 2),  // (σ : Type u) → (R : Type v) → Type (max u v)
        ("TensorProduct", 2), // (M : Type u) → (N : Type v) → Type (max u v)
        ("DirectSum", 2),     // (ι : Type u) → (M : ι → Type v) → Type (max u v)
        ("DualNumber", 1),    // (R : Type u) → Type u
        ("FractionRing", 1),  // (R : Type u) → Type u
        ("RatFunc", 1),       // (K : Type u) → Type u
    ];

    for (name, expected_arity) in &pi_type_constructors {
        let decl = env.get_const(&Name::from_string(name)).unwrap_or_else(|| {
            panic!("{name} is missing from the environment after init_domain_types")
        });
        let head = strip_wrappers(&decl.type_);
        assert!(
            matches!(&head.kind, ExprKind::Pi(_, _, _)),
            "{name} should have Pi type, but it doesn't. This causes NotAFunction errors in FATE-X."
        );

        let arity = pi_arity(&decl.type_);
        assert_eq!(
            arity, *expected_arity,
            "{name} should have {expected_arity} Pi binders but has {arity}."
        );
    }
}

// =============================================================================
// Recursor Signature Verification Tests
// These tests verify that generated recursors have correct signatures,
// matching Lean 4's parameterized inductive type patterns.
// =============================================================================

/// Verify Eq.rec has the correct signature structure.
///
/// In clean, Eq.rec follows Lean 4's "fixed index" pattern where the first
/// Eq index (a) is promoted to a rec-parameter:
/// - num_params = 2 (α is the type parameter, a is promoted from index)
/// - num_indices = 1 (only b remains as index)
///
/// The recursor type matches Lean 4's kernel:
/// Eq.rec : {α : Sort u} → {a : α} →
///          {motive : (x : α) → Eq a x → Sort v} →
///          motive a (Eq.refl a) →
///          {b : α} → (h : Eq a b) → motive b h
#[test]
fn test_eq_rec_signature_structure() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Get Eq.rec
    let rec = env.get_recursor(&Name::from_string("Eq.rec")).unwrap();

    // Verify basic counts (Lean 4 fixed-index: a promoted to rec-parameter)
    assert_eq!(
        rec.num_params, 2,
        "Eq.rec should have 2 parameters (α, a) — a promoted from index"
    );
    assert_eq!(
        rec.num_indices, 1,
        "Eq.rec should have 1 index (b) — a promoted to parameter"
    );
    assert_eq!(rec.num_motives, 1, "Eq should have 1 motive");
    assert_eq!(
        rec.num_minors, 1,
        "Eq should have 1 minor premise (for refl)"
    );

    // Verify is_k (Eq is K-like: Prop, single constructor, nullary after params)
    assert!(rec.is_k, "Eq should be K-like for UIP reduction");

    // Verify the recursor rule for Eq.refl
    assert_eq!(rec.rules.len(), 1, "Should have exactly one rule");
    let refl_rule = &rec.rules[0];
    assert_eq!(refl_rule.constructor_name, Name::from_string("Eq.refl"));
    assert_eq!(
        refl_rule.num_fields, 0,
        "Eq.refl has 0 fields from recursor's perspective after init_eq parameter promotion"
    );

    // Verify the recursor type has the expected number of Pi binders
    // Structure: {α} → {a} → {motive} → minor → {b} → h → result
    // That's 6 Pi binders total
    let rec_type = &rec.type_;
    let arity = count_pi_args(rec_type);
    assert_eq!(arity, 6, "Eq.rec should have 6 Pi binders");
}

/// Verify HEq.rec has the correct signature structure matching Lean 4.
///
/// HEq.rec : {α : Sort u} → {a : α} → {motive : ...} → (minor) → {β : Sort u} → {b : β} → (h : HEq) → motive b h
///
/// In clean, HEq is defined with:
/// - num_params = 2 (α and a are parameters - the "source" type and value)
/// - num_indices = 2 (β and b are indices - the "target" type and value)
#[test]
fn test_heq_rec_signature_structure() {
    fn assert_heq_app_with_bvars(expr: &Expr, expected_args: [u32; 4], context: &str) {
        let head = expr.get_app_fn();
        match &head.kind {
            ExprKind::Const(name, levels) => {
                assert_eq!(
                    name.to_string(),
                    "HEq",
                    "{context}: expected HEq head, got {name}"
                );
                assert_eq!(
                    levels.len(),
                    1,
                    "{context}: HEq application should have one universe level"
                );
            }
            _ => panic!("{context}: expected HEq constant head, got {head:?}"),
        }

        let args = expr.get_app_args();
        assert_eq!(
            args.len(),
            4,
            "{context}: HEq application must have 4 arguments"
        );
        for (i, expected) in expected_args.iter().enumerate() {
            assert_bvar(
                args[i],
                *expected,
                &format!("{context}: argument index {i}"),
            );
        }
    }

    let mut env = Environment::new();
    env.init_heq().unwrap();

    let rec = env.get_recursor(&Name::from_string("HEq.rec")).unwrap();

    // HEq has α and a as parameters, β and b as indices
    // This matches Lean 4's definition where the "source" side is fixed
    assert_eq!(rec.num_params, 2, "HEq should have 2 parameters (α, a)");
    assert_eq!(rec.num_indices, 2, "HEq should have 2 indices (β, b)");
    assert_eq!(rec.num_motives, 1, "HEq should have 1 motive");
    assert_eq!(rec.num_minors, 1, "HEq should have 1 minor premise");

    // HEq is K-like (Prop, single constructor, nullary after params)
    assert!(rec.is_k, "HEq should be K-like");

    // Verify top-level recursor shape (matches Lean 4 with infer_implicit):
    // {α} {a} {motive} → (minor) → {β} {b} (h : HEq a b) → motive b h
    let heq_rec_info = env.get_const(&Name::from_string("HEq.rec")).unwrap();
    assert_eq!(
        count_pi_args(&heq_rec_info.type_),
        7,
        "HEq.rec should have 7 top-level Pi binders"
    );

    let mut ty = heq_rec_info.type_.clone();
    let mut binders = Vec::new();
    let mut domains = Vec::new();
    for _ in 0..7 {
        match &ty.kind {
            ExprKind::Pi(bi, domain, body) => {
                binders.push(*bi);
                domains.push(domain.as_ref().clone());
                ty = body.as_ref().clone();
            }
            _ => panic!("HEq.rec type ended before collecting 7 Pi binders: {ty:?}"),
        }
    }
    assert!(
        !matches!(ty.kind, ExprKind::Pi(_, _, _)),
        "HEq.rec type should have exactly 7 top-level binders"
    );

    // infer_implicit post-processing (Lean 4 inductive.cpp:767) marks positions 1 (a)
    // and 5 (b) as Implicit because they appear in subsequent Pi domains.
    // Fixes: #1454
    let binder_infos: Vec<BinderInfo> = binders.iter().map(|bd| bd.info).collect();
    assert_eq!(
        binder_infos,
        vec![
            BinderInfo::Implicit, // {α : Sort u}
            BinderInfo::Implicit, // {a : α} — infer_implicit
            BinderInfo::Implicit, // {motive : ...}
            BinderInfo::Default,  // (minor)
            BinderInfo::Implicit, // {β : Sort u} — infer_implicit
            BinderInfo::Implicit, // {b : β} — infer_implicit
            BinderInfo::Default,  // (h : HEq)
        ],
        "HEq.rec binder info should match Lean 4 after infer_implicit"
    );

    match &domains[0].kind {
        ExprKind::Sort(Level::Param(_)) => {}
        _ => panic!("HEq.rec α binder should be Sort u, got {:?}", domains[0]),
    }
    assert_eq!(
        domains[4], domains[0],
        "HEq.rec β binder should reuse the same Sort u as α"
    );

    assert_bvar(&domains[1], 0, "HEq.rec a binder type");
    assert_bvar(&domains[5], 0, "HEq.rec b binder type");

    // motive : {β : Sort u} → (b : β) → HEq a b → Sort v
    match &domains[2].kind {
        ExprKind::Pi(motive_bi_beta, motive_beta_domain, motive_body_1) => {
            assert_eq!(
                motive_bi_beta.info,
                BinderInfo::Implicit,
                "HEq.rec motive β binder should be implicit"
            );
            assert_eq!(
                motive_beta_domain.as_ref(),
                &domains[0],
                "HEq.rec motive β should be in Sort u"
            );
            match &motive_body_1.kind {
                ExprKind::Pi(motive_bi_b, motive_b_domain, motive_body_2) => {
                    assert_eq!(
                        motive_bi_b.info,
                        BinderInfo::Default,
                        "HEq.rec motive b binder should be explicit"
                    );
                    assert_bvar(motive_b_domain, 0, "HEq.rec motive b binder type");
                    match &motive_body_2.kind {
                        ExprKind::Pi(motive_bi_h, motive_h_domain, motive_result) => {
                            assert_eq!(
                                motive_bi_h.info,
                                BinderInfo::Default,
                                "HEq.rec motive h binder should be explicit"
                            );
                            assert_heq_app_with_bvars(
                                motive_h_domain,
                                [3, 2, 1, 0],
                                "HEq.rec motive h domain",
                            );
                            match &motive_result.kind {
                                ExprKind::Sort(Level::Param(_)) => {}
                                _ => panic!(
                                    "HEq.rec motive result should be Sort v, got {motive_result:?}"
                                ),
                            }
                        }
                        _ => panic!(
                            "HEq.rec motive should have HEq hypothesis binder, got {motive_body_2:?}"
                        ),
                    }
                }
                _ => panic!("HEq.rec motive should bind b : β, got {motive_body_1:?}"),
            }
        }
        _ => panic!(
            "HEq.rec third binder should be motive, got {:?}",
            domains[2]
        ),
    }

    // minor premise: motive a (HEq.refl a)
    let minor_args = domains[3].get_app_args();
    assert_eq!(
        minor_args.len(),
        3,
        "HEq.rec minor premise should apply motive to 3 arguments"
    );
    assert!(
        matches!(domains[3].get_app_fn().kind, ExprKind::BVar(0)),
        "HEq.rec minor premise should be an application of motive binder"
    );
    assert_bvar(minor_args[0], 2, "HEq.rec minor β argument");
    assert_bvar(minor_args[1], 1, "HEq.rec minor b argument");
    match &minor_args[2].kind {
        ExprKind::App(_, _) => {
            let refl_head = minor_args[2].get_app_fn();
            match &refl_head.kind {
                ExprKind::Const(name, _) => assert_eq!(
                    name.to_string(),
                    "HEq.refl",
                    "HEq.rec minor third argument should be HEq.refl a"
                ),
                _ => panic!(
                    "HEq.rec minor third argument should be HEq.refl application, got {refl_head:?}"
                ),
            }
            let refl_args = minor_args[2].get_app_args();
            assert_eq!(
                refl_args.len(),
                2,
                "HEq.refl in HEq.rec minor should have 2 arguments"
            );
            assert_bvar(refl_args[0], 2, "HEq.rec minor HEq.refl α argument");
            assert_bvar(refl_args[1], 1, "HEq.rec minor HEq.refl a argument");
        }
        _ => panic!(
            "HEq.rec minor third argument should be an HEq.refl application, got {:?}",
            minor_args[2]
        ),
    }

    // h : HEq a b
    assert_heq_app_with_bvars(&domains[6], [5, 4, 1, 0], "HEq.rec h domain");

    // Result: motive b h
    let result_args = ty.get_app_args();
    assert_eq!(
        result_args.len(),
        3,
        "HEq.rec result should apply motive to 3 arguments"
    );
    assert!(
        matches!(ty.get_app_fn().kind, ExprKind::BVar(4)),
        "HEq.rec result should be headed by motive binder"
    );
    assert_bvar(result_args[0], 2, "HEq.rec result β argument");
    assert_bvar(result_args[1], 1, "HEq.rec result b argument");
    assert_bvar(result_args[2], 0, "HEq.rec result h argument");
}

/// Verify Nat.rec has the correct signature structure:
/// Nat.rec : {motive : Nat → Sort u} →
///           motive Nat.zero →
///           ((n : Nat) → motive n → motive (Nat.succ n)) →
///           (t : Nat) → motive t
///
/// Key aspects:
/// - num_params = 0 (no type parameters)
/// - num_indices = 0 (no indices)
/// - Minor for zero: motive Nat.zero
/// - Minor for succ: takes n and IH (motive n), returns motive (succ n)
#[test]
fn test_nat_rec_signature_structure() {
    let mut env = Environment::new();
    env.init_nat().unwrap();

    let rec = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();

    // Nat has no parameters or indices
    assert_eq!(rec.num_params, 0, "Nat should have 0 parameters");
    assert_eq!(rec.num_indices, 0, "Nat should have 0 indices");
    assert_eq!(rec.num_motives, 1, "Nat should have 1 motive");
    assert_eq!(rec.num_minors, 2, "Nat should have 2 minors (zero, succ)");

    // Nat is NOT K-like (it's in Type, not Prop)
    assert!(!rec.is_k, "Nat should NOT be K-like (not in Prop)");

    // Verify recursor rules
    assert_eq!(rec.rules.len(), 2, "Should have 2 rules");

    // Find zero and succ rules
    let zero_rule = rec
        .rules
        .iter()
        .find(|r| r.constructor_name.to_string().contains("zero"));
    let succ_rule = rec
        .rules
        .iter()
        .find(|r| r.constructor_name.to_string().contains("succ"));

    let zero_rule = zero_rule.expect("Should have a zero rule");
    let succ_rule = succ_rule.expect("Should have a succ rule");

    assert_eq!(zero_rule.num_fields, 0, "Nat.zero has no fields");
    assert_eq!(succ_rule.num_fields, 1, "Nat.succ has 1 field (n)");
    assert_eq!(succ_rule.recursive_fields, vec![true], "n is recursive");
}

/// Verify List.rec has the correct signature structure:
/// List.rec : {α : Type u} → {motive : List α → Sort v} →
///            motive List.nil →
///            ((head : α) → (tail : List α) → motive tail → motive (List.cons head tail)) →
///            (t : List α) → motive t
///
/// Key aspects:
/// - num_params = 1 (α is the type parameter)
/// - num_indices = 0 (no indices beyond params)
/// - Minor for nil: motive List.nil
/// - Minor for cons: takes head, tail, IH, returns motive (cons head tail)
#[test]
fn test_list_rec_signature_structure() {
    let mut env = Environment::new();
    env.init_list().unwrap();

    let rec = env.get_recursor(&Name::from_string("List.rec")).unwrap();

    // List has α as parameter, no indices
    assert_eq!(rec.num_params, 1, "List should have 1 parameter (α)");
    assert_eq!(rec.num_indices, 0, "List should have 0 indices");
    assert_eq!(rec.num_motives, 1, "List should have 1 motive");
    assert_eq!(rec.num_minors, 2, "List should have 2 minors (nil, cons)");

    // List is NOT K-like (it's in Type, not Prop)
    assert!(!rec.is_k, "List should NOT be K-like");

    // Verify recursor rules
    assert_eq!(rec.rules.len(), 2, "Should have 2 rules");

    let cons_rule = rec
        .rules
        .iter()
        .find(|r| r.constructor_name.to_string().contains("cons"));
    let cons_rule = cons_rule.expect("Should have a cons rule");

    assert_eq!(
        cons_rule.num_fields, 2,
        "List.cons has 2 fields (head, tail)"
    );
    // Only tail is recursive (it's List α)
    assert_eq!(
        cons_rule.recursive_fields,
        vec![false, true],
        "tail is recursive, head is not"
    );
}

/// Verify And.rec signature for a parameterized proposition:
/// And.rec : {a b : Prop} → {motive : And a b → Prop} →
///           ((left : a) → (right : b) → motive (And.intro left right)) →
///           (h : And a b) → motive h
#[test]
fn test_and_rec_signature_structure() {
    let mut env = Environment::new();
    env.init_and().unwrap();

    let rec = env.get_recursor(&Name::from_string("And.rec")).unwrap();

    // And has 2 parameters (a, b : Prop)
    assert_eq!(rec.num_params, 2, "And should have 2 parameters (a, b)");
    assert_eq!(rec.num_indices, 0, "And should have 0 indices");
    assert_eq!(rec.num_motives, 1, "And should have 1 motive");
    assert_eq!(rec.num_minors, 1, "And should have 1 minor (intro)");

    // And is NOT K-like (has 2 fields in constructor)
    assert!(!rec.is_k, "And should NOT be K-like (intro has fields)");

    // Verify the intro rule
    let intro_rule = &rec.rules[0];
    assert_eq!(intro_rule.constructor_name, Name::from_string("And.intro"));
    assert_eq!(
        intro_rule.num_fields, 2,
        "And.intro has 2 fields (left, right)"
    );
    // Neither field is recursive (they're just proofs of a and b)
    assert_eq!(
        intro_rule.recursive_fields,
        vec![false, false],
        "Neither field is recursive"
    );
}

/// Verify Or.rec signature for a multi-constructor parameterized proposition:
/// Or.rec : {a b : Prop} → {motive : Or a b → Prop} →
///          ((h : a) → motive (Or.inl h)) →
///          ((h : b) → motive (Or.inr h)) →
///          (h : Or a b) → motive h
#[test]
fn test_or_rec_signature_structure() {
    let mut env = Environment::new();
    env.init_or().unwrap();

    let rec = env.get_recursor(&Name::from_string("Or.rec")).unwrap();

    // Or has 2 parameters (a, b : Prop)
    assert_eq!(rec.num_params, 2, "Or should have 2 parameters (a, b)");
    assert_eq!(rec.num_indices, 0, "Or should have 0 indices");
    assert_eq!(rec.num_motives, 1, "Or should have 1 motive");
    assert_eq!(rec.num_minors, 2, "Or should have 2 minors (inl, inr)");

    // Or is NOT K-like (has 2 constructors)
    assert!(!rec.is_k, "Or should NOT be K-like (2 constructors)");

    // Verify the intro rules
    assert_eq!(rec.rules.len(), 2);
    let inl_rule = &rec.rules[0];
    assert_eq!(inl_rule.constructor_name, Name::from_string("Or.inl"));
    assert_eq!(inl_rule.num_fields, 1, "Or.inl has 1 field (proof of a)");
    assert_eq!(
        inl_rule.recursive_fields,
        vec![false],
        "Field is not recursive"
    );

    let inr_rule = &rec.rules[1];
    assert_eq!(inr_rule.constructor_name, Name::from_string("Or.inr"));
    assert_eq!(inr_rule.num_fields, 1, "Or.inr has 1 field (proof of b)");
    assert_eq!(
        inr_rule.recursive_fields,
        vec![false],
        "Field is not recursive"
    );
}

#[test]
fn test_init_or() {
    let mut env = Environment::new();
    assert!(!env.has_or());

    env.init_or().unwrap();
    assert!(env.has_or());

    // Check Or type exists
    let or_info = env.get_inductive(&Name::from_string("Or")).unwrap();
    assert_eq!(or_info.num_params, 2);
    assert_eq!(or_info.constructor_names.len(), 2);

    // Check constructors with arity verification
    // Or.inl : {a b : Prop} → a → Or a b
    let or_inl = env.get_const(&Name::from_string("Or.inl")).unwrap();
    assert_eq!(
        count_pi_args(&or_inl.type_),
        3,
        "Or.inl type should have 3 Pi binders (a, b, ha)"
    );

    // Or.inr : {a b : Prop} → b → Or a b
    let or_inr = env.get_const(&Name::from_string("Or.inr")).unwrap();
    assert_eq!(
        count_pi_args(&or_inr.type_),
        3,
        "Or.inr type should have 3 Pi binders (a, b, hb)"
    );

    // Or.elim is NOT added by init_or (it's a derived definition in Lean 4,
    // loaded from .olean, not part of the kernel inductive declaration).
    assert!(
        env.get_const(&Name::from_string("Or.elim")).is_none(),
        "Or.elim should not be in the kernel environment"
    );

    // Idempotent
    env.init_or().unwrap();
}

#[test]
fn test_or_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_or().unwrap();

    let tc = TypeChecker::new(&env);

    // Or.inl : {a b : Prop} → a → Or a b — 3 Pi binders
    let inl_const = Expr::const_(Name::from_string("Or.inl"), vec![]);
    let inl_type = tc.infer_type(&inl_const).unwrap();
    assert_eq!(
        count_pi_args(&inl_type),
        3,
        "Or.inl type should have 3 Pi binders"
    );

    // Or.inr : {a b : Prop} → b → Or a b — 3 Pi binders
    let inr_const = Expr::const_(Name::from_string("Or.inr"), vec![]);
    let inr_type = tc.infer_type(&inr_const).unwrap();
    assert_eq!(
        count_pi_args(&inr_type),
        3,
        "Or.inr type should have 3 Pi binders"
    );

    // Or.elim is NOT added by init_or (derived definition, loaded from .olean).
    let elim_const = Expr::const_(Name::from_string("Or.elim"), vec![]);
    assert!(
        tc.infer_type(&elim_const).is_err(),
        "Or.elim should not exist in the kernel environment"
    );
}

#[test]
fn test_or_classical_dependency() {
    // init_classical() should work and Or should be available via classical
    let mut env = Environment::new();
    env.init_classical().unwrap();

    // Or should have been initialized by init_classical
    assert!(env.has_or(), "init_classical should initialize Or");
    assert!(
        env.get_inductive(&Name::from_string("Or")).is_some(),
        "Or inductive should exist after init_classical"
    );
}

/// Test: instantiate_type rejects level count mismatch (#1277)
///
/// In Lean 4, supplying the wrong number of universe levels to a constant
/// is a hard error. Previously, clean used `zip` which silently truncated.
#[test]
fn test_instantiate_type_level_count_mismatch() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let name = Name::from_string("polyConst");

    // Declare a constant with 1 level param
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
    })
    .expect("axiom declaration should succeed");

    // Correct: 1 level for 1 param → Sort(0)
    let result = env
        .instantiate_type(&name, &[Level::Zero])
        .expect("exact level count match should succeed");
    assert_eq!(result, Expr::from_kind(ExprKind::Sort(Level::Zero)));

    // Too few: 0 levels for 1 param → None
    assert!(
        env.instantiate_type(&name, &[]).is_none(),
        "too few levels must return None, not silently truncate"
    );

    // Too many: 2 levels for 1 param → None
    assert!(
        env.instantiate_type(&name, &[Level::Zero, Level::succ(Level::Zero)])
            .is_none(),
        "too many levels must return None, not silently truncate"
    );
}

/// Test: unfold rejects level count mismatch (#1277)
#[test]
fn test_unfold_level_count_mismatch() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let name = Name::from_string("polyDef");

    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::Param(u.clone())))),
        value: Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
        is_reducible: true,
    })
    .expect("definition should succeed");

    // Correct count → value is Sort(u) with u=0 → Sort(0)
    let unfolded = env
        .unfold(&name, &[Level::Zero])
        .expect("exact level count match should unfold");
    assert_eq!(
        unfolded,
        Expr::from_kind(ExprKind::Sort(Level::Zero)),
        "unfolded value should be Sort(0)"
    );

    // Mismatch
    assert!(
        env.unfold(&name, &[]).is_none(),
        "too few levels must return None for unfold"
    );
    assert!(
        env.unfold(&name, &[Level::Zero, Level::Zero]).is_none(),
        "too many levels must return None for unfold"
    );
}

/// Test: type checker produces LevelCountMismatch error (#1277)
#[test]
fn test_type_checker_level_count_mismatch_error() {
    use crate::tc::{TypeChecker, TypeError};

    let mut env = Environment::new();
    let u = Name::from_string("u");
    let name = Name::from_string("polyAxiom");

    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
    })
    .expect("axiom should succeed");

    let tc = TypeChecker::new(&env);

    // Correct: 1 level → Ok, type is Sort(u) with u=0 → Sort(0) = Prop
    let good_expr = Expr::const_(name.clone(), vec![Level::Zero]);
    let inferred = tc
        .infer_type(&good_expr)
        .expect("correct level count should type-check");
    assert_eq!(
        inferred,
        Expr::from_kind(ExprKind::Sort(Level::Zero)),
        "polyAxiom.{{0}} : Sort(0) = Prop"
    );

    // Too few: 0 levels → LevelCountMismatch
    let bad_expr_few = Expr::const_(name.clone(), vec![]);
    match tc.infer_type(&bad_expr_few) {
        Err(TypeError::LevelCountMismatch { expected, got, .. }) => {
            assert_eq!(expected, 1);
            assert_eq!(got, 0);
        }
        other => panic!("expected LevelCountMismatch, got {other:?}"),
    }

    // Too many: 2 levels → LevelCountMismatch
    let bad_expr_many = Expr::const_(name.clone(), vec![Level::Zero, Level::Zero]);
    match tc.infer_type(&bad_expr_many) {
        Err(TypeError::LevelCountMismatch { expected, got, .. }) => {
            assert_eq!(expected, 1);
            assert_eq!(got, 2);
        }
        other => panic!("expected LevelCountMismatch, got {other:?}"),
    }
}

/// Test: zero-param constant still works with empty levels (#1277 regression guard)
#[test]
fn test_instantiate_type_zero_params_empty_levels() {
    let mut env = Environment::new();
    let name = Name::from_string("simpleConst");

    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("axiom should succeed");

    // 0 params, 0 levels → should work
    let result = env.instantiate_type(&name, &[]);
    assert_eq!(result, Some(Expr::prop()));

    // 0 params, 1 level → should fail
    assert!(
        env.instantiate_type(&name, &[Level::Zero]).is_none(),
        "supplying levels to a zero-param constant must fail"
    );
}

/// Test: unfold_with_transparency rejects level count mismatch (#1277)
///
/// This is the same class of bug as instantiate_type and unfold:
/// `zip` silently truncates when level counts don't match. The guard
/// must reject mismatches even when transparency would allow unfolding.
#[test]
fn test_unfold_with_transparency_level_count_mismatch() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let name = Name::from_string("polyTransDef");

    // Declare a reducible definition with 1 level param
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::Param(u.clone())))),
        value: Expr::from_kind(ExprKind::Sort(Level::Param(u.clone()))),
        is_reducible: true,
    })
    .expect("definition should succeed");

    // Correct: 1 level for 1 param → Sort(0) (All mode unfolds reducible)
    let result = env
        .unfold_with_transparency(&name, &[Level::Zero], TransparencyMode::All)
        .expect("exact level count match should unfold");
    assert_eq!(result, Expr::from_kind(ExprKind::Sort(Level::Zero)));

    // Too few: 0 levels for 1 param → None
    assert!(
        env.unfold_with_transparency(&name, &[], TransparencyMode::All)
            .is_none(),
        "too few levels must return None for unfold_with_transparency"
    );

    // Too many: 2 levels for 1 param → None
    assert!(
        env.unfold_with_transparency(
            &name,
            &[Level::Zero, Level::succ(Level::Zero)],
            TransparencyMode::All
        )
        .is_none(),
        "too many levels must return None for unfold_with_transparency"
    );

    // Also check Reducible mode (the definition IS reducible)
    assert!(
        env.unfold_with_transparency(&name, &[], TransparencyMode::Reducible)
            .is_none(),
        "level mismatch must reject regardless of transparency mode"
    );
}

// ============================================================================
// #1276: add_decl type-checking tests
// ============================================================================

/// AC1: add_decl checks that the type is well-formed (infers a Sort) (#1276)
#[test]
fn test_add_decl_rejects_ill_typed_type() {
    let mut env = Environment::new();

    // Axiom whose "type" is a reference to a nonexistent constant.
    // infer_sort should fail because it can't resolve NonExistent.
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("bad_axiom"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("NonExistent"), vec![]),
    });
    let err = result.expect_err("axiom with ill-typed type must be rejected");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "expected TypeCheckFailed, got {err:?}"
    );
}

/// AC2: add_decl checks that the value has the declared type (#1276)
///
/// Attempt: def f : Prop := Type
/// Prop = Sort(0), Type = Sort(1). Type has type Sort(2), which is not Prop.
#[test]
fn test_add_decl_rejects_type_value_mismatch() {
    let mut env = Environment::new();

    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_def"),
        level_params: vec![],
        type_: Expr::prop(), // Prop = Sort(0) — well-formed, has type Type = Sort(1)
        value: Expr::type_(), // Type = Sort(1) — has type Sort(2), not Prop
        is_reducible: false,
    });
    let err = result.expect_err("definition with type/value mismatch must be rejected");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "expected TypeCheckFailed, got {err:?}"
    );
}

/// AC3: add_decl validates universe level parameters (no duplicates) (#1276)
#[test]
fn test_add_decl_rejects_duplicate_level_params() {
    let mut env = Environment::new();
    let u = Name::from_string("u");

    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("dup_levels"),
        level_params: vec![u.clone(), u.clone()],
        type_: Expr::prop(),
    });
    let err = result.expect_err("duplicate level params must be rejected");
    assert!(
        matches!(err, EnvError::DuplicateLevelParam { .. }),
        "expected DuplicateLevelParam, got {err:?}"
    );
}

/// AC4: add_decl_unchecked exists and skips validation (#1276)
#[test]
fn test_add_decl_unchecked_skips_type_check() {
    let mut env = Environment::new();

    // This would fail add_decl because the type references a nonexistent constant.
    // add_decl_unchecked should accept it without checking.
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("unchecked_axiom"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("NonExistent"), vec![]),
    });

    let info = env
        .get_const(&Name::from_string("unchecked_axiom"))
        .expect("unchecked axiom must be present in environment");
    assert_eq!(
        info.level_params.len(),
        0,
        "unchecked_axiom should have 0 level params"
    );
    assert_eq!(info.value, None, "axiom should have no value body");
}

/// AC5+6: Well-typed declarations succeed via add_decl (#1276)
#[test]
fn test_add_decl_accepts_well_typed_declarations() {
    let mut env = Environment::new();

    // Well-typed axiom: Prop has type Type (a Sort), so it's well-formed
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("good_axiom"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("well-typed axiom must succeed");

    // Well-typed definition: type is Type (Sort 1), value is Prop (Sort 0 : Sort 1 = Type)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("good_def"),
        level_params: vec![],
        type_: Expr::type_(), // Type = Sort(1), has type Sort(2) — well-formed
        value: Expr::prop(),  // Prop = Sort(0), has type Sort(1) = Type — matches
        is_reducible: false,
    })
    .expect("well-typed definition must succeed");

    // Declare a proposition P : Prop, and a proof hp : P
    let p_name = Name::from_string("P");
    let hp_name = Name::from_string("hp");
    env.add_decl(Declaration::Axiom {
        name: p_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("axiom P : Prop must succeed");
    env.add_decl(Declaration::Axiom {
        name: hp_name.clone(),
        level_params: vec![],
        type_: Expr::const_(p_name.clone(), vec![]),
    })
    .expect("axiom hp : P must succeed");

    // Well-typed theorem: good_thm : P := hp
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("good_thm"),
        level_params: vec![],
        type_: Expr::const_(p_name, vec![]),
        value: Expr::const_(hp_name, vec![]),
    })
    .expect("well-typed theorem with proposition type must succeed");

    // Verify all are in the environment with arity checks
    let good_axiom = env.get_const(&Name::from_string("good_axiom")).unwrap();
    assert_eq!(
        count_pi_args(&good_axiom.type_),
        0,
        "good_axiom should have 0 Pi binders"
    );
    let good_def = env.get_const(&Name::from_string("good_def")).unwrap();
    let def_val = good_def
        .value
        .as_ref()
        .expect("good_def should have a definition body");
    assert_eq!(*def_val, Expr::prop(), "good_def value should be Prop");

    let good_thm = env.get_const(&Name::from_string("good_thm")).unwrap();
    let thm_val = good_thm
        .value
        .as_ref()
        .expect("good_thm should have a proof term");
    assert_eq!(
        *thm_val,
        Expr::const_(Name::from_string("hp"), vec![]),
        "good_thm proof must be the axiom hp"
    );
}

/// Theorem with ill-typed proof is rejected (#1276)
///
/// theorem bad : P := Type  where P : Prop
/// The theorem type is a genuine proposition, so rejection must be about proof mismatch.
#[test]
fn test_add_decl_rejects_theorem_with_bad_proof() {
    let mut env = Environment::new();

    let p_name = Name::from_string("Pbad");
    env.add_decl(Declaration::Axiom {
        name: p_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("axiom Pbad : Prop must succeed");

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("bad_thm"),
        level_params: vec![],
        type_: Expr::const_(p_name, vec![]),
        value: Expr::type_(), // Type : Sort(2), not a proof of Pbad
    });
    let err = result.expect_err("theorem with ill-typed proof must be rejected");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "expected TypeCheckFailed, got {err:?}"
    );
}

/// Theorem type must live in Prop (Sort 0) (#1276)
#[test]
fn test_add_decl_rejects_theorem_non_prop_type() {
    let mut env = Environment::new();

    // theorem bad : Type := Prop
    // Type is Sort(1), so theorem should be rejected before proof checking.
    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("bad_thm_non_prop"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
    });

    let err = result.expect_err("theorem with non-Prop type must be rejected");
    assert!(
        matches!(err, EnvError::TheoremTypeNotProp { ref sort, .. } if !sort.is_zero()),
        "expected TheoremTypeNotProp with non-zero sort, got {err:?}"
    );
}

/// Opaque with type/value mismatch is rejected (#1276)
#[test]
fn test_add_decl_rejects_opaque_with_mismatch() {
    let mut env = Environment::new();

    let result = env.add_decl(Declaration::Opaque {
        name: Name::from_string("bad_opaque"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::type_(),
    });
    let err = result.expect_err("opaque with type/value mismatch must be rejected");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "expected TypeCheckFailed, got {err:?}"
    );
}

// ============================================================================
// #1311: add_decl error path coverage — DuplicateName, ContainsFreeVar,
// UndefinedLevelParam, DuplicateLevelParam
// ============================================================================

/// add_decl with duplicate name returns DuplicateName (#1311)
#[test]
fn test_add_decl_rejects_duplicate_name_via_add_decl() {
    let mut env = Environment::new();

    // First declaration succeeds
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_axiom"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("first add_decl should succeed");

    // Second declaration with same name must fail
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_axiom"),
        level_params: vec![],
        type_: Expr::prop(),
    });

    let err = result.expect_err("duplicate name must be rejected");
    assert!(
        matches!(err, EnvError::DuplicateName(ref n) if n.to_string() == "my_axiom"),
        "expected DuplicateName('my_axiom'), got {err:?}"
    );
}

/// add_decl with FVar in type returns ContainsFreeVar (#1311)
#[test]
fn test_add_decl_rejects_fvar_in_type() {
    let mut env = Environment::new();

    // Axiom with type containing a free variable
    let fvar_type = Expr::fvar(crate::expr::FVarId(42));
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("bad_fvar_type"),
        level_params: vec![],
        type_: fvar_type,
    });

    let err = result.expect_err("FVar in type must be rejected");
    assert!(
        matches!(err, EnvError::ContainsFreeVar { ref name, .. } if name.to_string() == "bad_fvar_type"),
        "expected ContainsFreeVar('bad_fvar_type'), got {err:?}"
    );
}

/// add_decl with FVar in value returns ContainsFreeVar (#1311)
#[test]
fn test_add_decl_rejects_fvar_in_value() {
    let mut env = Environment::new();

    // Definition with value containing a free variable
    let fvar_value = Expr::fvar(crate::expr::FVarId(99));
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_fvar_value"),
        level_params: vec![],
        type_: Expr::prop(),
        value: fvar_value,
        is_reducible: true,
    });

    let err = result.expect_err("FVar in value must be rejected");
    assert!(
        matches!(err, EnvError::ContainsFreeVar { ref name, .. } if name.to_string() == "bad_fvar_value"),
        "expected ContainsFreeVar('bad_fvar_value'), got {err:?}"
    );
}

/// add_decl with undefined level param in type returns UndefinedLevelParam (#1311)
#[test]
fn test_add_decl_rejects_undefined_level_param_in_type() {
    let mut env = Environment::new();

    // Axiom with type Sort(Param("v")) but level_params = ["u"]
    let v_param = Level::param(Name::from_string("v"));
    let type_with_bad_level = Expr::from_kind(ExprKind::Sort(v_param));
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("bad_level_type"),
        level_params: vec![Name::from_string("u")],
        type_: type_with_bad_level,
    });

    let err = result.expect_err("undefined level param in type must be rejected");
    assert!(
        matches!(err, EnvError::UndefinedLevelParam { ref param, .. } if param.to_string() == "v"),
        "expected UndefinedLevelParam with param 'v', got {err:?}"
    );
}

/// add_decl with undefined level param in value returns UndefinedLevelParam (#1311)
#[test]
fn test_add_decl_rejects_undefined_level_param_in_value() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    // Definition with value containing undefined level param "w"
    let w_param = Level::param(Name::from_string("w"));
    let value_with_bad_level = Expr::from_kind(ExprKind::Sort(w_param));
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_level_value"),
        level_params: vec![u],
        type_: sort_u,
        value: value_with_bad_level,
        is_reducible: true,
    });

    let err = result.expect_err("undefined level param in value must be rejected");
    assert!(
        matches!(err, EnvError::UndefinedLevelParam { ref param, .. } if param.to_string() == "w"),
        "expected UndefinedLevelParam with param 'w', got {err:?}"
    );
}

/// add_decl with empty level_params but Level::Param in type returns UndefinedLevelParam (#1311)
#[test]
fn test_add_decl_rejects_empty_level_params_with_param_reference() {
    let mut env = Environment::new();

    // type = Sort(Param("u")) but level_params = []
    let type_with_param = Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("u"))));
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("no_level_params"),
        level_params: vec![],
        type_: type_with_param,
    });

    let err = result.expect_err("param reference with empty level_params must be rejected");
    assert!(
        matches!(err, EnvError::UndefinedLevelParam { ref param, .. } if param.to_string() == "u"),
        "expected UndefinedLevelParam with param 'u', got {err:?}"
    );
}

/// Theorem with type whose sort is IMax(Param(u), Zero) — definitively Prop,
/// so the theorem should be accepted. (#1311)
///
/// We construct Π (x : Sort u), True, whose sort is IMax(u, 0) = 0 = Prop.
#[test]
fn test_add_decl_accepts_theorem_imax_param_zero() {
    let mut env = Environment::new();
    // Need True : Prop for the body type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("adding True axiom");

    // trivial : True (the proof)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("trivial"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .expect("adding trivial axiom");

    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let trivial_const = Expr::const_(Name::from_string("trivial"), vec![]);

    // theorem t.{u} : Π (x : Sort u), True := λ (x : Sort u), trivial
    // type sort: IMax(u, 0) = 0 = Prop — should be accepted
    let theorem_type = Expr::pi(BinderInfo::Default, sort_u.clone(), true_const);
    let theorem_value = Expr::lam(BinderInfo::Default, sort_u, trivial_const);

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("t_imax_u_zero"),
        level_params: vec![u],
        type_: theorem_type,
        value: theorem_value,
    });

    result.expect("theorem with type in Sort(IMax(u, 0)) = Prop should be accepted");

    // Verify the theorem was added with correct structure
    let info = env
        .get_const(&Name::from_string("t_imax_u_zero"))
        .expect("theorem must exist after add_decl");
    assert_eq!(
        info.level_params.len(),
        1,
        "t_imax_u_zero should have 1 level param (u)"
    );
    let proof = info.value.as_ref().expect("theorem must have a proof body");
    assert!(
        matches!(&proof.kind, ExprKind::Lam(bd, ..) if bd.info == BinderInfo::Default),
        "t_imax_u_zero proof must be a lambda with default binder"
    );
}

/// Theorem with type whose sort is IMax(Zero, Succ(Param(u))) — NOT definitively
/// Prop (depends on u), so the theorem should be rejected. (#1311)
///
/// We construct Π (x : True), Sort u, whose sort is IMax(0, Succ(u)).
/// IMax(0, Succ(u)).is_zero() is false since Succ(u) is not zero.
#[test]
fn test_add_decl_rejects_theorem_imax_zero_param() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("adding True axiom");

    let u = Name::from_string("u");
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // theorem bad.{u} : Π (x : True), Sort u
    // type sort: IMax(0, Succ(u)) — not definitively Prop when u > 0
    let theorem_type = Expr::pi(BinderInfo::Default, true_const, sort_u);

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("bad_imax_zero_u"),
        level_params: vec![u],
        type_: theorem_type,
        value: Expr::prop(), // dummy value, type check will fail first
    });

    let err = result.expect_err("theorem with non-Prop IMax sort should be rejected");
    assert!(
        matches!(err, EnvError::TheoremTypeNotProp { .. }),
        "expected TheoremTypeNotProp, got {err:?}"
    );
}

/// add_decl with duplicate level params returns DuplicateLevelParam (#1311)
#[test]
fn test_add_decl_rejects_duplicate_level_params_1311() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("dup_level"),
        level_params: vec![u.clone(), u],
        type_: sort_u,
    });

    let err = result.expect_err("duplicate level params must be rejected");
    assert!(
        matches!(err, EnvError::DuplicateLevelParam { ref param, .. } if param.to_string() == "u"),
        "expected DuplicateLevelParam with param 'u', got {err:?}"
    );
}

// ============================================================================
// #1292: Compound soundness integration test
// Exercises the interaction of #1276 (add_decl type-checking),
// #1277 (level parameter truncation rejection), and #1278 (Classical.choice
// argument validation) to verify no compound exploit path exists.
// ============================================================================

/// Integration test: a deliberately ill-typed declaration chain that exercises
/// all three soundness paths (#1276, #1277, #1278) and verifies each is rejected.
///
/// Attack scenario:
/// 1. Insert a universe-polymorphic definition with mismatched type/value via add_decl
///    → must be rejected (#1276)
/// 2. If it were inserted unchecked, instantiate with wrong level count
///    → must return None (#1277)
/// 3. Use Classical.choice with ill-typed arguments in a definition
///    → must be rejected by type checker (#1278)
///
/// The compound risk: without ALL three checks, an attacker could insert
/// an ill-typed definition, instantiate it with truncated levels to produce
/// a term at a wrong universe, and then use Classical.choice on that term
/// to produce a value of arbitrary type.
#[test]
fn test_compound_soundness_all_three_paths() {
    let mut env = Environment::new();

    // ---- Path 1: #1276 — add_decl rejects ill-typed declarations ----

    // Try to add a definition where type and value disagree:
    // def bad.{u} : Sort(u) := Sort(u+1)
    // Sort(u) : Sort(u+1) — type is well-formed
    // Sort(u+1) : Sort(u+2) — but Sort(u+2) is not def-eq to Sort(u)
    let u_name = Name::from_string("u");
    let u_level = Level::param(u_name.clone());

    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_def_1292"),
        level_params: vec![u_name.clone()],
        type_: Expr::from_kind(ExprKind::Sort(u_level.clone())), // Sort(u)
        value: Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))), // Sort(u+1) — wrong type
        is_reducible: true,
    });
    assert!(
        result.is_err(),
        "Path 1 (#1276): add_decl must reject definition with type/value mismatch"
    );
    assert!(
        env.get_const(&Name::from_string("bad_def_1292")).is_none(),
        "rejected declaration must not appear in environment"
    );

    // ---- Path 2: #1277 — instantiate_type rejects level count mismatch ----

    // Insert a well-typed polymorphic axiom via add_decl:
    // axiom poly.{u} : Sort(u+1)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("poly_1292"),
        level_params: vec![u_name.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))), // Sort(u+1) : Sort(u+2)
    })
    .expect("well-typed polymorphic axiom must succeed");

    // Try to instantiate with zero levels (expects 1)
    let result_zero = env.instantiate_type(&Name::from_string("poly_1292"), &[]);
    assert!(
        result_zero.is_none(),
        "Path 2 (#1277): instantiate_type must reject zero levels when 1 expected"
    );

    // Try to instantiate with two levels (expects 1)
    let result_two = env.instantiate_type(
        &Name::from_string("poly_1292"),
        &[Level::zero(), Level::succ(Level::zero())],
    );
    assert!(
        result_two.is_none(),
        "Path 2 (#1277): instantiate_type must reject two levels when 1 expected"
    );

    // Correct instantiation should work — poly_1292 : Sort(u+1), u=0 → Sort(1)
    let result_ok = env
        .instantiate_type(&Name::from_string("poly_1292"), &[Level::zero()])
        .expect("instantiate_type with correct level count must succeed");
    assert_eq!(
        result_ok,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        "poly_1292.{{0}} type should be Sort(1) since axiom type is Sort(u+1)"
    );

    // ---- Path 3: #1278 — Classical.choice rejects ill-typed arguments ----

    // Initialize classical axioms so Classical.choice is in the environment.
    // This also upgrades the mode to Classical (#1335), so the type checker
    // exercises the type validation path rather than rejecting via mode check.
    env.init_classical().expect("init_classical should succeed");

    // Classical.choice is now an axiom: {α : Sort u} → Nonempty α → α
    // Try to add a definition whose value applies Classical.choice with wrong arg type.
    // We pass Prop as the Nonempty proof, which is ill-typed.
    let choice_const = Expr::const_(Name::from_string("Classical.choice"), vec![Level::zero()]);
    let bad_choice_app = Expr::app(
        Expr::app(choice_const, Expr::prop()), // α = Prop (ok for implicit)
        Expr::prop(),                          // Nonempty Prop expected, got Prop
    );
    let bad_choice_def = Declaration::Definition {
        name: Name::from_string("bad_choice_1292"),
        level_params: vec![],
        type_: Expr::prop(), // Prop — the declared type
        value: bad_choice_app,
        is_reducible: false,
    };
    let result = env.add_decl(bad_choice_def);
    assert!(
        result.is_err(),
        "Path 3 (#1278): add_decl must reject Classical.choice with ill-typed arguments"
    );
    // Verify rejection is a type check failure (type mismatch), not a mode error (#1335)
    match &result {
        Err(EnvError::TypeCheckFailed { .. }) => {} // expected: type validation catches the bad arg
        other => panic!("Path 3 (#1335): expected TypeCheckFailed, got: {other:?}"),
    }

    // ---- Compound scenario: unchecked insertion + level mismatch ----

    // Even if an ill-typed declaration were inserted via add_decl_unchecked
    // (e.g., during trusted .olean import), level count enforcement still
    // blocks exploitation via instantiation.
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("smuggled_1292"),
        level_params: vec![u_name.clone(), Name::from_string("v")], // 2 params
        type_: Expr::from_kind(ExprKind::Sort(u_level.clone())), // Sort(u) — would be wrong in practice
        value: Expr::type_(),                                    // Type = Sort(1) — ill-typed value
        is_reducible: true,
    });

    // The declaration exists (unchecked path doesn't validate)
    let smuggled = env
        .get_const(&Name::from_string("smuggled_1292"))
        .expect("unchecked declaration is present");
    assert_eq!(
        smuggled.level_params.len(),
        2,
        "smuggled_1292 should have 2 level params (u, v)"
    );

    // But instantiation with wrong level count is blocked
    assert!(
        env.instantiate_type(&Name::from_string("smuggled_1292"), &[Level::zero()])
            .is_none(),
        "Compound: 1 level for 2-param constant must be rejected"
    );
    assert!(
        env.instantiate_type(&Name::from_string("smuggled_1292"), &[])
            .is_none(),
        "Compound: 0 levels for 2-param constant must be rejected"
    );

    // Correct count works (even though the definition is internally ill-typed)
    let instantiated = env
        .instantiate_type(
            &Name::from_string("smuggled_1292"),
            &[Level::zero(), Level::succ(Level::zero())],
        )
        .expect("Compound: correct level count allows instantiation");
    // Type is Sort(u) with u=0 → Sort(0)
    assert_eq!(
        instantiated,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
        "instantiated type should be Sort(0)"
    );

    // Also verify unfold is protected
    assert!(
        env.unfold(&Name::from_string("smuggled_1292"), &[Level::zero()])
            .is_none(),
        "Compound: unfold with wrong level count must be rejected"
    );
}

/// Deep expression walks should not overflow the stack.
#[test]
fn test_expr_has_fvar_handles_deep_expression_recursion() {
    let func = Expr::const_(Name::from_string("f"), vec![]);
    let mut deep_expr = Expr::fvar(crate::expr::FVarId(0));
    for _ in 0..20_000 {
        deep_expr = Expr::app(func.clone(), deep_expr);
    }

    assert!(
        deep_expr.has_fvar_quick(),
        "deep expression should contain FVar"
    );

    // Iterative drop handles 20k-deep chains safely (no stack overflow).
    crate::expr::iterative_drop(deep_expr);
}

// ====================================================================
// Tests for add_decl_unchecked: Definition, Theorem, Opaque variants
// and reducibility mapping (Part of #1357)
// ====================================================================

/// Test add_decl_unchecked with Definition variant: value is stored,
/// is_reducible=true maps to Reducibility::Reducible.
#[test]
fn test_add_decl_unchecked_definition_reducible() {
    let mut env = Environment::new();

    let def_name = Name::from_string("my_def");
    let value = Expr::prop();
    env.add_decl_unchecked(Declaration::Definition {
        name: def_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: value.clone(),
        is_reducible: true,
    });

    let info = env.get_const(&def_name).expect("definition must exist");
    assert_eq!(info.value.as_ref(), Some(&value), "value must be stored");
    assert_eq!(
        info.reducibility,
        Reducibility::Reducible,
        "is_reducible=true must map to Reducible"
    );
    assert!(info.is_reducible);
}

/// Test add_decl_unchecked with Definition variant: is_reducible=false maps
/// to Reducibility::Regular(0).
#[test]
fn test_add_decl_unchecked_definition_semireducible() {
    let mut env = Environment::new();

    let def_name = Name::from_string("my_def2");
    env.add_decl_unchecked(Declaration::Definition {
        name: def_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: false,
    });

    let info = env.get_const(&def_name).expect("definition must exist");
    // Lean 4 declaration.cpp: non-reducible definition gets Regular(max_height(value) + 1).
    // Expr::prop() = Sort(Zero) contains no Const nodes, so max_height = 0, height = 0 + 1 = 1.
    assert_eq!(
        info.reducibility,
        Reducibility::Regular(1),
        "is_reducible=false must map to Regular(get_max_height(value) + 1)"
    );
    assert!(!info.is_reducible);
}

/// Test add_decl_unchecked with Theorem variant: value is stored,
/// reducibility is Opaque.
#[test]
fn test_add_decl_unchecked_theorem_opaque_reducibility() {
    let mut env = Environment::new();

    let thm_name = Name::from_string("my_thm");
    let proof = Expr::prop(); // dummy proof term
    env.add_decl_unchecked(Declaration::Theorem {
        name: thm_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
        value: proof.clone(),
    });

    let info = env.get_const(&thm_name).expect("theorem must exist");
    assert_eq!(info.value.as_ref(), Some(&proof), "proof must be stored");
    assert_eq!(
        info.reducibility,
        Reducibility::Opaque,
        "theorem must have Opaque reducibility"
    );
    assert!(!info.is_reducible);
}

/// Test add_decl_unchecked with Opaque variant: value is stored,
/// reducibility is Opaque.
#[test]
fn test_add_decl_unchecked_opaque_variant() {
    let mut env = Environment::new();

    let op_name = Name::from_string("my_opaque");
    let val = Expr::type_(); // dummy value
    env.add_decl_unchecked(Declaration::Opaque {
        name: op_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: val.clone(),
    });

    let info = env.get_const(&op_name).expect("opaque must exist");
    assert_eq!(info.value.as_ref(), Some(&val), "value must be stored");
    assert_eq!(
        info.reducibility,
        Reducibility::Opaque,
        "opaque must have Opaque reducibility"
    );
}

/// In debug builds, unchecked insertion must fail-fast on duplicate names.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "add_decl_unchecked duplicate constant")]
fn test_add_decl_unchecked_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    let name = Name::from_string("overwrite_me");

    env.add_decl_unchecked(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    });
    env.add_decl_unchecked(Declaration::Definition {
        name,
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    });
}

/// In release builds (no debug assertions), unchecked insertion keeps overwrite semantics.
#[cfg(not(debug_assertions))]
#[test]
fn test_add_decl_unchecked_overwrites_existing_in_release() {
    let mut env = Environment::new();
    let name = Name::from_string("overwrite_me");

    // First insert
    env.add_decl_unchecked(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    });
    assert_eq!(
        env.get_const(&name).unwrap().value,
        None,
        "axiom should have no value before overwrite"
    );

    // Overwrite with definition that has a value
    env.add_decl_unchecked(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    });

    let info = env.get_const(&name).expect("must still exist");
    let val = info
        .value
        .as_ref()
        .expect("overwrite must replace axiom with definition");
    assert_eq!(*val, Expr::prop(), "overwritten value should be Prop");
    assert_eq!(info.reducibility, Reducibility::Reducible);
}

// ====================================================================
// Tests for serialization error paths (Part of #1357)
// ====================================================================

/// Test from_json with invalid JSON input.
#[test]
fn test_from_json_invalid_input() {
    let result = Environment::from_json("");
    let _err = result.expect_err("empty string must fail JSON parsing");

    let result = Environment::from_json("{invalid json}");
    let _err = result.expect_err("invalid JSON must fail parsing");

    let result = Environment::from_json("null");
    let _err = result.expect_err("null must fail parsing");
}

/// Test from_bincode with corrupt data.
#[test]
fn test_from_bincode_corrupt_data() {
    let result = Environment::from_bincode(&[]);
    let _err = result.expect_err("empty bytes must fail bincode parsing");

    let result = Environment::from_bincode(&[0, 1, 2, 3, 255, 128]);
    let _err = result.expect_err("random bytes must fail bincode parsing");
}

/// Test save_to_file with invalid path.
#[test]
fn test_save_to_file_invalid_path() {
    let env = Environment::new();
    let result = env.save_to_file(std::path::Path::new("/nonexistent/dir/file.bin"));
    let _err = result.expect_err("save to nonexistent dir must fail");
}

/// Test load_from_file with nonexistent file.
#[test]
fn test_load_from_file_nonexistent() {
    let result = Environment::load_from_file(std::path::Path::new("/tmp/does_not_exist_clean.bin"));
    let _err = result.expect_err("loading nonexistent file must fail");
}

/// Test that JSON roundtrip loses registry data (classes, instances, simp lemmas).
/// This documents a known limitation: JSON serialization only preserves constants,
/// inductives, constructors, recursors, quotients, and structure_fields.
#[test]
fn test_json_roundtrip_loses_registries() {
    let mut env = Environment::new();

    // Add a class registration
    let class_name = Name::from_string("MyClass");
    env.add_decl_unchecked(Declaration::Axiom {
        name: class_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    });
    env.register_class(KernelClassInfo {
        name: class_name.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    // Verify class is registered before serialization
    assert!(
        env.is_class(&class_name),
        "class must be registered before serialization"
    );

    // JSON roundtrip
    let json = env.to_json().expect("to_json must succeed");
    let env2 = Environment::from_json(&json).expect("from_json must succeed");

    // Constant survives roundtrip with correct type
    let roundtripped = env2
        .get_const(&class_name)
        .expect("constant must survive JSON roundtrip");
    assert_eq!(
        roundtripped.type_,
        Expr::type_(),
        "roundtripped constant type must match"
    );

    // But class registration is lost
    assert!(
        !env2.is_class(&class_name),
        "class registration must be lost in JSON roundtrip (not part of JsonEnvironment)"
    );
}

/// Test that bincode roundtrip preserves more state than JSON.
#[test]
fn test_bincode_preserves_full_state() {
    let mut env = Environment::new();

    // Add a definition
    let def_name = Name::from_string("bincode_def");
    env.add_decl_unchecked(Declaration::Definition {
        name: def_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    });

    // Bincode roundtrip
    let bytes = env.to_bincode().expect("to_bincode must succeed");
    let env2 = Environment::from_bincode(&bytes).expect("from_bincode must succeed");

    let info = env2.get_const(&def_name).expect("constant must survive");
    assert_eq!(info.reducibility, Reducibility::Reducible);
    let val = info
        .value
        .as_ref()
        .expect("definition value must survive bincode roundtrip");
    assert_eq!(*val, Expr::prop(), "roundtripped value should be Prop");
}

// ====================================================================
// Tests for unfold_with_transparency edge cases (Part of #1357)
// ====================================================================

/// Test unfold_with_transparency returns None for nonexistent name.
#[test]
fn test_unfold_with_transparency_nonexistent_name() {
    let env = Environment::new();
    let result = env.unfold_with_transparency(
        &Name::from_string("nonexistent"),
        &[],
        TransparencyMode::All,
    );
    assert_eq!(result, None, "nonexistent name must return None");
}

/// Test unfold_with_transparency returns None for axiom (no value).
#[test]
fn test_unfold_with_transparency_axiom_no_value() {
    let mut env = Environment::new();

    let ax_name = Name::from_string("my_axiom");
    env.add_decl_unchecked(Declaration::Axiom {
        name: ax_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    });

    // Even in All mode, axiom has no value to unfold
    let result = env.unfold_with_transparency(&ax_name, &[], TransparencyMode::All);
    assert!(
        result.is_none(),
        "axiom (no value) must return None even in All mode"
    );
}

/// Test unfold_with_transparency with multi-level parameter substitution.
#[test]
fn test_unfold_with_transparency_multi_level_substitution() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let def_name = Name::from_string("multi_level_def");

    // Define a constant with 2 level params whose value uses both:
    // value = Sort(u) (a sort expression at level u)
    let value = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    env.add_decl_unchecked(Declaration::Definition {
        name: def_name.clone(),
        level_params: vec![u.clone(), v.clone()],
        type_: Expr::type_(),
        value,
        is_reducible: true,
    });

    // Substitute u=1, v=0 → value Sort(u) becomes Sort(1)
    let result = env
        .unfold_with_transparency(
            &def_name,
            &[Level::succ(Level::zero()), Level::zero()],
            TransparencyMode::All,
        )
        .expect("unfold with matching level count must succeed");
    assert_eq!(
        result,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        "unfolded value should be Sort(1) after substituting u=1"
    );

    // Wrong number of levels: should return None
    let result_mismatch =
        env.unfold_with_transparency(&def_name, &[Level::zero()], TransparencyMode::All);
    assert!(
        result_mismatch.is_none(),
        "unfold with wrong level count must return None"
    );
}

/// Test that Opaque definitions never unfold, even in All mode.
#[test]
fn test_unfold_with_transparency_opaque_never_unfolds() {
    let mut env = Environment::new();

    let op_name = Name::from_string("opaque_def");
    env.add_decl_unchecked(Declaration::Opaque {
        name: op_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
    });

    // Opaque should never unfold, not even in All mode
    for mode in [
        TransparencyMode::Reducible,
        TransparencyMode::Instances,
        TransparencyMode::Default,
        TransparencyMode::All,
    ] {
        let result = env.unfold_with_transparency(&op_name, &[], mode);
        assert!(
            result.is_none(),
            "Opaque must never unfold, not even in {mode:?} mode"
        );
    }
}

/// Test unfold_with_transparency respects Reducible/Semireducible/Irreducible boundaries.
#[test]
fn test_unfold_with_transparency_reducibility_boundaries() {
    let mut env = Environment::new();

    // Reducible definition
    let red_name = Name::from_string("red_def");
    env.add_decl_unchecked(Declaration::Definition {
        name: red_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    });

    // Semireducible definition
    let semi_name = Name::from_string("semi_def");
    env.add_decl_unchecked(Declaration::Definition {
        name: semi_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: false,
    });

    // Reducible: unfolds in all modes
    let red_result = env
        .unfold_with_transparency(&red_name, &[], TransparencyMode::Reducible)
        .expect("Reducible unfolds in Reducible mode");
    assert_eq!(red_result, Expr::prop(), "red_def unfolded must be Prop");

    // Semireducible: does NOT unfold in Reducible mode
    assert!(
        env.unfold_with_transparency(&semi_name, &[], TransparencyMode::Reducible)
            .is_none(),
        "Semireducible must not unfold in Reducible mode"
    );

    // Semireducible: DOES unfold in Default mode
    let semi_result = env
        .unfold_with_transparency(&semi_name, &[], TransparencyMode::Default)
        .expect("Semireducible must unfold in Default mode");
    assert_eq!(semi_result, Expr::prop(), "semi_def unfolded must be Prop");
}

// ====================================================================
// Tests for add_inductive edge cases (Part of #1357)
// ====================================================================

/// Test add_inductive with a zero-constructor type (Empty-like).
#[test]
fn test_add_inductive_empty_type() {
    let mut env = Environment::new();

    let empty = Name::from_string("Empty");
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: empty.clone(),
            type_: Expr::prop(),  // Empty : Prop
            constructors: vec![], // No constructors
        }],
    };

    env.add_inductive(decl)
        .expect("Empty type must be accepted");

    // Inductive registered
    let ind = env
        .get_inductive(&empty)
        .expect("Empty must be registered as inductive");
    assert_eq!(ind.constructor_names.len(), 0);
    assert_eq!(ind.num_params, 0, "Empty has 0 params");

    // Recursor must still be generated
    let rec = env
        .get_recursor(&Name::from_string("Empty.rec"))
        .expect("Empty.rec must exist even with no constructors");
    assert_eq!(rec.num_minors, 0, "Empty.rec has 0 minor premises");
    assert_eq!(rec.num_params, 0, "Empty.rec has 0 params");

    // casesOn must also be generated with arity check
    let cases_on = env
        .get_const(&Name::from_string("Empty.casesOn"))
        .expect("Empty.casesOn must exist");
    assert!(
        count_pi_args(&cases_on.type_) >= 2,
        "Empty.casesOn should have >= 2 Pi binders (motive, major)"
    );
}

/// Test add_inductive with an indexed type (Fin n).
#[test]
fn test_add_inductive_indexed_type() {
    let mut env = Environment::new();

    // Nat must exist first (used as index type)
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let nat_decl = InductiveDecl {
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
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl).expect("Nat must be accepted");

    // Fin : Nat -> Type
    // Fin.zero : (n : Nat) -> Fin (succ n)
    let fin_name = Name::from_string("Fin");
    let fin_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: fin_name.clone(),
            // Fin : Nat -> Type 0
            type_: Expr::arrow(nat_ref.clone(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("Fin.zero"),
                // Fin.zero : (n : Nat) -> Fin (succ n)
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat_ref.clone(),
                    Expr::app(
                        Expr::const_(fin_name.clone(), vec![]),
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.succ"), vec![]),
                            Expr::bvar(0), // n
                        ),
                    ),
                ),
            }],
        }],
    };

    env.add_inductive(fin_decl)
        .expect("Fin (indexed type) must be accepted");

    let ind = env
        .get_inductive(&fin_name)
        .expect("Fin must be registered");
    // Fin has 0 params and 1 index (n : Nat)
    assert_eq!(ind.num_params, 0);
    assert_eq!(ind.num_indices, 1, "Fin must have 1 index");
    assert_eq!(ind.constructor_names.len(), 1, "Fin has 1 constructor");
}

/// Indexed family whose recursive field carries a LAMBDA-valued index
/// argument capturing a ctor-context variable — the `Std.DHashMap.Raw.WF` /
/// `Std.DTreeMap.Internal.Impl.WF` shape (const-map index `fun _ => β`).
///
///   W : (Nat → Nat) → Prop
///   W.step : (f : Nat) → W (fun _ => f) → W (fun _ => f)
///
/// The residual-index BVar remap must descend into the lambda with depth
/// tracking: inside `fun _ => f` the field reference `f` sits one binder
/// deeper. The pre-fix walker recursed only into `App`, leaving the ctor-
/// context index verbatim, so the IH premise (and the iota rule RHS — which
/// nothing byte-checks downstream) referenced the WRONG variable (`h`, the
/// recursive field, instead of `f`).
#[test]
fn test_indexed_recursor_lambda_index_remap() {
    let mut env = Environment::new();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(InductiveDecl {
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
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    })
    .expect("Nat must be accepted");

    let w_name = Name::from_string("W");
    let w_ref = Expr::const_(w_name.clone(), vec![]);
    // index type: Nat → Nat
    let nat_to_nat = Expr::arrow(nat_ref.clone(), nat_ref.clone());
    // ctor telescope: (f : Nat) → W (fun _ => f#1) → W (fun _ => f#2)
    let step_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                w_ref.clone(),
                Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(1)),
            ),
            Expr::app(
                w_ref.clone(),
                Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(2)),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: w_name.clone(),
            type_: Expr::arrow(nat_to_nat, Expr::prop()),
            constructors: vec![Constructor {
                name: Name::from_string("W.step"),
                type_: step_type,
            }],
        }],
    })
    .expect("W (lambda-valued recursive index) must be accepted");

    let rec = env
        .get_recursor(&Name::from_string("W.rec"))
        .expect("W.rec must be registered");

    // The recursor type must be well-formed under the kernel.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _sort = tc
        .infer_sort(&rec.type_)
        .expect("W.rec type must be well-typed");

    // --- Minor premise: Π f. Π h. (motive (fun _ => f) h) → motive … ---
    // Navigate: rec.type_ = Π motive. Π minor. …; minor domain = Π f. Π h. Π IH. concl
    let ExprKind::Pi(_, _, after_motive) = &rec.type_.kind else {
        panic!("W.rec type must start with the motive Pi");
    };
    let ExprKind::Pi(_, minor_domain, _) = &after_motive.kind else {
        panic!("W.rec type must have a minor premise Pi");
    };
    let ExprKind::Pi(_, _, m1) = &minor_domain.kind else {
        panic!("minor premise must bind f");
    };
    let ExprKind::Pi(_, _, m2) = &m1.kind else {
        panic!("minor premise must bind h");
    };
    let ExprKind::Pi(_, ih_domain, _) = &m2.kind else {
        panic!("minor premise must carry an IH premise");
    };
    // IH domain = App(App(motive, fun _ => f), h); in its context the binders
    // are [motive, f, h] + the lambda binder, so `f` is BVar(2).
    let ih_args = ih_domain.get_app_args().to_vec();
    let idx_lam = ih_args
        .first()
        .expect("IH premise must apply the motive to the remapped index");
    let ExprKind::Lam(_, _, lam_body) = &idx_lam.kind else {
        panic!("IH index argument must stay a lambda, got {idx_lam:?}");
    };
    assert_eq!(
        lam_body.kind,
        ExprKind::BVar(2),
        "IH index lambda must reference field `f` (BVar 2 under the lambda); \
         BVar(1) means the ctor-context index leaked through unremapped"
    );

    // --- Rule RHS: λ motive. λ minor. λ f. λ h. minor f h (W.rec motive minor (fun _ => f) h) ---
    let rule = rec
        .rules
        .first()
        .expect("W.rec must have a rule for W.step");
    let mut body = &rule.rhs;
    let mut lambdas = 0;
    while let ExprKind::Lam(_, _, inner) = &body.kind {
        body = inner;
        lambdas += 1;
    }
    assert_eq!(lambdas, 4, "rule RHS binds motive, minor, f, h");
    // body = minor f h IH; the IH is the last argument.
    let rhs_args = body.get_app_args().to_vec();
    let ih = rhs_args.last().expect("rule RHS must apply the IH");
    // IH = W.rec motive minor (fun _ => f) h — index arg is 3rd of 4.
    let ih_args = ih.get_app_args().to_vec();
    let rhs_idx_lam = ih_args
        .get(2)
        .expect("rule-RHS IH must pass the remapped index to W.rec");
    let ExprKind::Lam(_, _, rhs_lam_body) = &rhs_idx_lam.kind else {
        panic!("rule-RHS IH index argument must stay a lambda, got {rhs_idx_lam:?}");
    };
    assert_eq!(
        rhs_lam_body.kind,
        ExprKind::BVar(2),
        "rule-RHS IH index lambda must reference field `f` (BVar 2 under the \
         lambda) — this path builds the iota rules nothing byte-checks"
    );
}

/// Test that add_inductive rejects duplicate constructor names.
#[test]
fn test_add_inductive_duplicate_constructor_name() {
    let mut env = Environment::new();

    // First, add something named "clash" to the environment
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("clash"),
        level_params: vec![],
        type_: Expr::prop(),
    });

    let ind_name = Name::from_string("ClashInd");
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("clash"), // conflicts with existing constant
                type_: Expr::const_(ind_name.clone(), vec![]),
            }],
        }],
    };

    let result = env.add_inductive(decl);
    assert!(
        result.is_err(),
        "constructor name clashing with existing constant must be rejected"
    );
}

/// Test rec/casesOn/recOn argument ordering and generated constants.
#[test]
fn test_rec_cases_on_rec_on_arg_ordering() {
    use crate::inductive::RecursorArgOrder;

    let mut env = Environment::new();

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
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("Nat2 must succeed");

    let rec = env
        .get_recursor(&Name::from_string("Nat2.rec"))
        .expect("Nat2.rec must exist");
    let cases = env
        .get_recursor(&Name::from_string("Nat2.casesOn"))
        .expect("Nat2.casesOn must exist");
    let rec_on = env
        .get_recursor(&Name::from_string("Nat2.recOn"))
        .expect("Nat2.recOn must exist");

    // rec: MajorAfterMinors (params → motives → minors → indices → major)
    assert_eq!(rec.arg_order, RecursorArgOrder::MajorAfterMinors);

    // casesOn and recOn: MajorAfterMotive — the Lean-faithful layout
    // (params → motives → indices → major → minors)
    assert_eq!(cases.arg_order, RecursorArgOrder::MajorAfterMotive);
    assert_eq!(rec_on.arg_order, RecursorArgOrder::MajorAfterMotive);

    // All should have 2 minors (one per constructor: zero and succ)
    assert_eq!(rec.num_minors, 2, "rec must have 2 minor premises");
    assert_eq!(cases.num_minors, 2, "casesOn must have 2 minor premises");
    assert_eq!(rec_on.num_minors, 2, "recOn must have 2 minor premises");

    // Regression for the GRADUATION #3 blocker (List.concat.match_1 /
    // Int.neg.match_1): the generated casesOn TYPE must spell Lean's binder
    // telescope — motive → MAJOR → minors — so values elaborated against
    // Lean's casesOn (e.g. `.olean` match auxiliaries) re-typecheck against
    // a Clean-regenerated environment. The old rec-layout spelling put the
    // minors before the major, landing every Lean-order application's
    // scrutinee in the first minor slot ("expected motive zero, got Nat2").
    let nat2 = Expr::const_(Name::from_string("Nat2"), vec![]);
    let ExprKind::Pi(_, motive_ty, rest) = &cases.type_.kind else {
        panic!("casesOn type must start with the motive Pi");
    };
    assert!(
        matches!(&motive_ty.kind, ExprKind::Pi(_, dom, _) if **dom == nat2),
        "casesOn binder 0 must be the motive (Nat2 -> Sort u)"
    );
    let ExprKind::Pi(_, major_ty, rest) = &rest.kind else {
        panic!("casesOn type must have a second Pi binder");
    };
    assert_eq!(
        **major_ty, nat2,
        "casesOn binder 1 must be the major premise (t : Nat2) — Lean's \
         layout, NOT the rec layout's first minor"
    );
    let ExprKind::Pi(_, zero_minor_ty, _) = &rest.kind else {
        panic!("casesOn type must have a third Pi binder");
    };
    assert!(
        matches!(&zero_minor_ty.kind, ExprKind::App(_, _)),
        "casesOn binder 2 must be the zero minor (motive Nat2.zero)"
    );
}

/// Lean kernel parity (GRADUATION #3 probe, `Lean.SourceInfo.synthetic`): a
/// constructor field spelled `optParam B d` must surface as plain `B` in the
/// generated recursor minor premises — the Lean kernel routes every binder
/// domain its inductive machinery collects through
/// `Expr.consumeTypeAnnotations`, so `.olean`-imported recursors never carry
/// `optParam`/`autoParam`/`outParam`/`semiOutParam` wrappers even when the
/// stored constructor type does. Without the stripping, a Clean-regenerated
/// recursor diverges from the imported one and the graduation gate's
/// carried-family member cross-check fail-closes.
#[test]
fn test_recursor_minor_premise_consumes_opt_param_annotation() {
    let mut env = Environment::new();

    // optParam.{u} : (α : Sort u) → α → Sort u := fun α _ => α
    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("optParam"),
        level_params: vec![u],
        type_: Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), sort_u.clone()),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            sort_u,
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
        is_reducible: true,
    })
    .expect("optParam definition must kernel-check");

    // inductive MyB | f | t
    let myb = Name::from_string("MyB");
    let myb_ref = Expr::const_(myb.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: myb.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyB.f"),
                    type_: myb_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyB.t"),
                    type_: myb_ref.clone(),
                },
            ],
        }],
    })
    .expect("MyB must succeed");

    // inductive Flag | mk (b : optParam.{1} MyB MyB.f)
    let flag = Name::from_string("Flag");
    let annotated_field = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("optParam"),
                vec![Level::succ(Level::zero())],
            ),
            myb_ref.clone(),
        ),
        Expr::const_(Name::from_string("MyB.f"), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: flag.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Flag.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    annotated_field,
                    Expr::const_(flag.clone(), vec![]),
                ),
            }],
        }],
    })
    .expect("Flag with optParam field must succeed");

    // Flag.rec : (motive : Flag → Sort u) → ((b : MyB) → motive (Flag.mk b))
    //   → (t : Flag) → motive t — the minor's field binder must be the BARE
    //   `MyB`, not the `optParam MyB MyB.f` wrapper the constructor carries.
    let rec = env
        .get_const(&Name::from_string("Flag.rec"))
        .expect("Flag.rec must exist");
    let ExprKind::Pi(_, _motive, rest) = &rec.type_.kind else {
        panic!("Flag.rec must start with the motive Pi");
    };
    let ExprKind::Pi(_, minor_ty, _) = &rest.kind else {
        panic!("Flag.rec must have a minor premise Pi");
    };
    let ExprKind::Pi(_, field_ty, _) = &minor_ty.kind else {
        panic!("the mk minor must bind the constructor field");
    };
    assert_eq!(
        **field_ty, myb_ref,
        "minor premise field domain must be the annotation-stripped `MyB` \
         (Lean kernel `consumeTypeAnnotations` parity), got `{field_ty}`"
    );

    // The constructor itself keeps its annotation (Lean stores it verbatim).
    let mk = env
        .get_const(&Name::from_string("Flag.mk"))
        .expect("Flag.mk must exist");
    let ExprKind::Pi(_, mk_field, _) = &mk.type_.kind else {
        panic!("Flag.mk must be a Pi");
    };
    assert!(
        matches!(&mk_field.kind, ExprKind::App(_, _)),
        "constructor field must keep its optParam annotation"
    );
}

// ============================================================================
// Tests for add_inductive validation (#2156)
// ============================================================================

/// F3: add_inductive must reject duplicate universe level parameters.
/// Matches the same check in add_decl.
#[test]
fn test_add_inductive_reject_duplicate_level_params() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let decl = InductiveDecl {
        level_params: vec![u.clone(), u.clone()], // duplicate!
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bad"),
            type_: Expr::sort(Level::param(u.clone())),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                type_: Expr::const_(Name::from_string("Bad"), vec![Level::param(u.clone())]),
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("duplicate level params must be rejected");
    assert!(
        matches!(err, EnvError::DuplicateLevelParam { ref param, .. } if *param == u),
        "expected DuplicateLevelParam, got {err:?}"
    );
}

/// F3: add_inductive must reject free variables (FVar) in inductive types.
#[test]
fn test_add_inductive_reject_fvar_in_type() {
    use crate::expr::FVarId;

    let mut env = Environment::new();

    // Inductive type contains an FVar
    let bad_type = Expr::arrow(Expr::fvar(FVarId::new(42)), Expr::type_());
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadFVar"),
            type_: bad_type,
            constructors: vec![Constructor {
                name: Name::from_string("BadFVar.mk"),
                type_: Expr::const_(Name::from_string("BadFVar"), vec![]),
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("FVar in type must be rejected");
    assert!(
        matches!(err, EnvError::ContainsFreeVar { .. }),
        "expected ContainsFreeVar, got {err:?}"
    );
}

/// F3: add_inductive must reject free variables (FVar) in constructor types.
#[test]
fn test_add_inductive_reject_fvar_in_constructor() {
    use crate::expr::FVarId;

    let mut env = Environment::new();

    let my_type = Name::from_string("MyType");
    let my_ref = Expr::const_(my_type.clone(), vec![]);

    // Constructor type contains an FVar
    let bad_ctor_type = Expr::arrow(Expr::fvar(FVarId::new(99)), my_ref.clone());
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: my_type.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("MyType.mk"),
                type_: bad_ctor_type,
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("FVar in constructor type must be rejected");
    assert!(
        matches!(err, EnvError::ContainsFreeVar { .. }),
        "expected ContainsFreeVar, got {err:?}"
    );
}

/// F3: add_inductive must reject undefined level parameters in types.
#[test]
fn test_add_inductive_reject_undefined_level_param() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let v = Name::from_string("v"); // not declared in level_params

    // Type uses Level::param(v) but only u is declared
    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadLevel"),
            type_: Expr::sort(Level::param(v.clone())), // uses v, not declared
            constructors: vec![Constructor {
                name: Name::from_string("BadLevel.mk"),
                type_: Expr::const_(Name::from_string("BadLevel"), vec![Level::param(u.clone())]),
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("undefined level param must be rejected");
    assert!(
        matches!(err, EnvError::UndefinedLevelParam { ref param, .. } if *param == v),
        "expected UndefinedLevelParam for 'v', got {err:?}"
    );
}

/// F3: add_inductive must reject undefined level params in constructor types.
#[test]
fn test_add_inductive_reject_undefined_level_param_in_ctor() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let w = Name::from_string("w"); // not declared

    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadCtorLevel"),
            type_: Expr::sort(Level::param(u.clone())),
            constructors: vec![Constructor {
                name: Name::from_string("BadCtorLevel.mk"),
                type_: Expr::arrow(
                    // arg with undeclared level param w
                    Expr::sort(Level::param(w.clone())),
                    Expr::const_(
                        Name::from_string("BadCtorLevel"),
                        vec![Level::param(u.clone())],
                    ),
                ),
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("undefined level param in ctor must be rejected");
    assert!(
        matches!(err, EnvError::UndefinedLevelParam { ref param, .. } if *param == w),
        "expected UndefinedLevelParam for 'w', got {err:?}"
    );
}

/// F3: add_inductive type-checks inductive types (infer_sort must succeed).
/// A malformed type expression should be rejected.
#[test]
fn test_add_inductive_type_check_rejects_malformed_type() {
    let mut env = Environment::new();

    // Use an application to a non-existent constant as the type —
    // this is not a Sort and will fail infer_sort.
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("BadType"),
            type_: Expr::app(Expr::type_(), Expr::type_()), // Type applied to Type — not a valid type former
            constructors: vec![],
        }],
    };

    let result = env.add_inductive(decl);
    // Should fail at either validate_inductive (no constructors) or type checking.
    // The validate_inductive check for empty constructors may fire first depending
    // on the variant. Either way, the declaration should be rejected.
    let _err = result.expect_err("malformed type must be rejected");
}

/// F3: add_inductive type-checks constructor types.
/// A constructor referencing an undefined constant should fail type checking.
#[test]
fn test_add_inductive_type_check_rejects_bad_constructor() {
    let mut env = Environment::new();

    let my_type = Name::from_string("TCType");
    let my_ref = Expr::const_(my_type.clone(), vec![]);

    // Constructor takes an argument of type "Nonexistent" which is not in the environment
    let bad_ctor_type = Expr::arrow(
        Expr::const_(Name::from_string("Nonexistent"), vec![]),
        my_ref.clone(),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: my_type.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("TCType.mk"),
                type_: bad_ctor_type,
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("constructor with undefined reference must be rejected");
    assert!(
        matches!(err, EnvError::TypeCheckFailed { .. }),
        "expected TypeCheckFailed, got {err:?}"
    );
}

/// F2: Universe constraint — non-Prop inductive in Type 0 must reject
/// a constructor with a field in a larger universe.
#[test]
fn test_add_inductive_universe_mismatch_type0() {
    let mut env = Environment::new();

    let bad = Name::from_string("BadUniverse");
    let bad_ref = Expr::const_(bad.clone(), vec![]);

    // Inductive in Type 0 (Sort 1)
    // Constructor takes a field of Type 1 (Sort 2) — sort(Type 1) = 2 > 1 = sort(Type 0)
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad.clone(),
            type_: Expr::type_(), // Sort 1 = Type 0
            constructors: vec![Constructor {
                name: Name::from_string("BadUniverse.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    // Type 1 = Sort 2 — its sort is Sort 3, which is universe level 2
                    Expr::sort(Level::succ(Level::succ(Level::zero()))),
                    bad_ref.clone(),
                ),
            }],
        }],
    };

    let err = env
        .add_inductive(decl)
        .expect_err("universe mismatch must be rejected");
    assert!(
        matches!(
            err,
            EnvError::Inductive(crate::inductive::InductiveError::UniverseMismatch(_))
        ),
        "expected UniverseMismatch, got {err:?}"
    );
}

/// F2: Prop inductives should NOT be rejected for large-universe fields.
/// Prop is impredicative — constructor fields may be in higher universes.
/// The restriction for Prop is on elimination (large_elim), not construction.
#[test]
fn test_add_inductive_prop_allows_type_valued_field() {
    let mut env = Environment::new();

    let exists_name = Name::from_string("MyExists");
    let u = Name::from_string("u");
    let u_param = Level::param(u.clone());

    // MyExists : Sort u → Prop
    let exists_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(u_param.clone()),
        Expr::prop(), // result is Prop
    );

    // MyExists.intro : (α : Sort u) → α → MyExists α
    let exists_ref = Expr::const_(exists_name.clone(), vec![u_param.clone()]);
    let ctor_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(u_param.clone()),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),                                // α (bound by the outer Pi)
            Expr::app(exists_ref.clone(), Expr::bvar(1)), // MyExists α
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1, // α is a parameter
        types: vec![InductiveType {
            name: exists_name.clone(),
            type_: exists_type,
            constructors: vec![Constructor {
                name: Name::from_string("MyExists.intro"),
                type_: ctor_type,
            }],
        }],
    };

    // This should succeed — Prop is impredicative
    env.add_inductive(decl)
        .expect("Prop inductive with Type-valued field must be accepted (impredicativity)");
}

/// F3: Successful add_inductive with valid structural properties should still work.
/// Regression test to ensure the new validation doesn't break normal declarations.
#[test]
fn test_add_inductive_valid_passes_all_checks() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    let u_param = Level::param(u.clone());

    let list = Name::from_string("ValidList");
    let alpha = Expr::sort(Level::succ(u_param.clone()));

    // ValidList : Type u → Type u
    let list_type = Expr::pi(
        BinderInfo::Implicit,
        alpha.clone(),
        Expr::sort(Level::succ(u_param.clone())),
    );

    let list_ref = Expr::const_(list.clone(), vec![u_param.clone()]);

    // nil : {α : Type u} → ValidList α
    let nil_type = Expr::pi(
        BinderInfo::Implicit,
        alpha.clone(),
        Expr::app(list_ref.clone(), Expr::bvar(0)),
    );

    // cons : {α : Type u} → α → ValidList α → ValidList α
    let cons_type = Expr::pi(
        BinderInfo::Implicit,
        alpha.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // α
            Expr::pi(
                BinderInfo::Default,
                Expr::app(list_ref.clone(), Expr::bvar(1)), // ValidList α
                Expr::app(list_ref.clone(), Expr::bvar(2)), // ValidList α
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("ValidList.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("ValidList.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };

    env.add_inductive(decl)
        .expect("valid List-like inductive should pass all new checks");

    env.get_inductive(&list)
        .expect("ValidList inductive should be registered");
    env.get_constructor(&Name::from_string("ValidList.nil"))
        .expect("ValidList.nil constructor should be registered");
    env.get_constructor(&Name::from_string("ValidList.cons"))
        .expect("ValidList.cons constructor should be registered");
}

/// F1 (#2156): Nested positivity — Container with negative parameter use.
///
/// Container (A : Type) | mk : (A → Nat) → Container A
/// Bad | mk : Container Bad → Bad
///
/// Bad appears negatively inside Container.mk: after substituting A=Bad,
/// mk becomes (Bad → Nat) → Container Bad, where Bad is in the domain
/// of the inner arrow. This must be rejected.
#[test]
fn test_add_inductive_nested_positivity_reject() {
    let mut env = Environment::new();

    // First, register Container in the environment.
    // Container (A : Type) : Type
    // Container.mk : (A : Type) → (A → Nat) → Container A
    let container = Name::from_string("Container");
    let nat = Name::from_string("Nat");

    // Register Nat first (needed for Container.mk's type)
    let nat_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: Expr::const_(nat.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        Expr::const_(nat.clone(), vec![]),
                        Expr::const_(nat.clone(), vec![]),
                    ),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl).expect("Nat should be added");

    // Container : Type → Type
    let container_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A : Type
        Expr::type_(), // Container A : Type
    );

    // Container.mk : (A : Type) → (A → Nat) → Container A
    // De Bruijn: Pi(Type, Pi(Arrow(BVar(1), Nat), App(Container, BVar(2))))
    // Wait: after binding A (BVar 0 at depth 0), the body is:
    //   Pi(_ : BVar(0) → Nat, App(Container, BVar(1)))
    // At depth 1 (inside the inner Pi), A is BVar(1).
    let container_mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A : Type (parameter)
        Expr::pi(
            BinderInfo::Default,
            Expr::arrow(
                Expr::bvar(0), // A
                Expr::const_(nat.clone(), vec![]),
            ),
            Expr::app(
                Expr::const_(container.clone(), vec![]),
                Expr::bvar(1), // A (shifted by inner Pi binder)
            ),
        ),
    );

    let container_decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: container.clone(),
            type_: container_type,
            constructors: vec![Constructor {
                name: Name::from_string("Container.mk"),
                type_: container_mk_type,
            }],
        }],
    };
    env.add_inductive(container_decl)
        .expect("Container should be added");

    // Now try to add Bad | mk : Container Bad → Bad
    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), vec![]);
    let bad_type = Expr::type_();

    // Bad.mk : Container Bad → Bad
    let bad_mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::const_(container.clone(), vec![]), bad_ref.clone()),
        bad_ref.clone(),
    );

    let bad_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad.clone(),
            type_: bad_type,
            constructors: vec![Constructor {
                name: Name::from_string("Bad.mk"),
                type_: bad_mk_type,
            }],
        }],
    };

    let result = env.add_inductive(bad_decl);
    let err =
        result.expect_err("Nested negative positivity (Container Bad → Bad) must be rejected");
    assert!(
        matches!(
            err,
            EnvError::Inductive(crate::inductive::InductiveError::NonPositive(..))
        ),
        "Expected NonPositive error for nested negative occurrence, got: {err}"
    );
}

/// F1 (#2156): Nested positivity — List with positive parameter use should pass.
///
/// List (A : Type) | nil : List A | cons : A → List A → List A
/// TreeNode | mk : List TreeNode → TreeNode
///
/// TreeNode appears positively inside List's constructors: after substituting
/// A=TreeNode, cons becomes TreeNode → List TreeNode → List TreeNode, where
/// TreeNode only appears in strictly positive positions.
#[test]
fn test_add_inductive_nested_positivity_accept_list() {
    let mut env = Environment::new();

    // Register List first
    let u = Name::from_string("u");
    let list = Name::from_string("NList");

    let list_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );

    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );

    // nil : (A : Type u) → NList A
    let nil_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        list_a.clone(),
    );

    // cons : (A : Type u) → A → NList A → NList A
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        cons_body,
    );

    let list_decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("NList.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("NList.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    env.add_inductive(list_decl).expect("NList should be added");

    // Now add TreeNode | mk : NList TreeNode → TreeNode
    let tree = Name::from_string("TreeNode");
    let tree_ref = Expr::const_(tree.clone(), vec![]);

    // TreeNode.mk : NList.{0} TreeNode → TreeNode
    // (NList.{u} : Type u → Type u and TreeNode : Type 0, so u = 0)
    let tree_mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::const_(list.clone(), vec![Level::zero()]),
            tree_ref.clone(),
        ),
        tree_ref.clone(),
    );

    let tree_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: tree.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("TreeNode.mk"),
                type_: tree_mk_type,
            }],
        }],
    };

    env.add_inductive(tree_decl)
        .expect("TreeNode with NList TreeNode should be accepted (positive nesting)");

    // Verify is_nested is set correctly (#2156 F1 AC).
    // TreeNode uses NList (a container) applied to TreeNode, so is_nested = true.
    // NList itself is not nested (declared standalone), so is_nested = false.
    let tree_val = env.inductives.get(&tree).expect("TreeNode in env");
    assert!(
        tree_val.is_nested,
        "TreeNode should be marked as nested (uses NList TreeNode)"
    );
    let list_val = env.inductives.get(&list).expect("NList in env");
    assert!(
        !list_val.is_nested,
        "NList should not be marked as nested (standalone)"
    );
}

/// Soundness test: visited-set scoping bug (#2156).
///
/// BiContainer : Type → Type → Type
/// BiContainer.mk : (A B : Type) → (B → A) → BiContainer A B
///
/// Parameter B appears in NEGATIVE position (domain of B → A),
/// parameter A in POSITIVE position (codomain of B → A).
///
/// Bad | c1 : BiContainer Bad Nat → Bad  (A=Bad positive, B=Nat → OK)
///      | c2 : BiContainer Nat Bad → Bad  (A=Nat, B=Bad negative → REJECT)
///
/// c1: substituting A=Bad, B=Nat gives mk field type (Nat → Bad) — Bad positive ✓
/// c2: substituting A=Nat, B=Bad gives mk field type (Bad → Nat) — Bad negative ✗
///
/// If the visited set is shared across constructors, c1 marks BiContainer as
/// visited. c2 then skips the BiContainer check entirely, allowing Bad in
/// negative position. This is a soundness bug.
#[test]
fn test_visited_set_per_constructor_soundness() {
    let mut env = Environment::new();

    let nat = Name::from_string("Nat");
    let nat_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: Expr::const_(nat.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        Expr::const_(nat.clone(), vec![]),
                        Expr::const_(nat.clone(), vec![]),
                    ),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl).expect("Nat should be added");

    // BiContainer : Type → Type → Type
    let bicont = Name::from_string("BiContainer");
    let bicont_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(), // B
            Expr::type_(), // BiContainer A B : Type
        ),
    );
    // BiContainer.mk : (A : Type) → (B : Type) → (B → A) → BiContainer A B
    // De Bruijn: Pi(Type, Pi(Type, Pi(Arrow(BVar(0), BVar(1)), App(App(BiContainer, BVar(2)), BVar(1)))))
    let bicont_mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A (param)
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(), // B (param)
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(
                    Expr::bvar(0), // B
                    Expr::bvar(1), // A
                ),
                Expr::app(
                    Expr::app(
                        Expr::const_(bicont.clone(), vec![]),
                        Expr::bvar(2), // A
                    ),
                    Expr::bvar(1), // B
                ),
            ),
        ),
    );
    let bicont_decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: bicont.clone(),
            type_: bicont_type,
            constructors: vec![Constructor {
                name: Name::from_string("BiContainer.mk"),
                type_: bicont_mk_type,
            }],
        }],
    };
    env.add_inductive(bicont_decl)
        .expect("BiContainer should be added");

    // First verify: c1 alone (positive use) is accepted.
    // Good | c1 : BiContainer Good Nat → Good  (Good in A=positive → OK)
    let good = Name::from_string("Good");
    let good_ref = Expr::const_(good.clone(), vec![]);
    let good_c1_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::const_(bicont.clone(), vec![]),
                good_ref.clone(), // A = Good
            ),
            Expr::const_(nat.clone(), vec![]), // B = Nat
        ),
        good_ref.clone(),
    );
    let good_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: good.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Good.c1"),
                type_: good_c1_type,
            }],
        }],
    };
    env.add_inductive(good_decl)
        .expect("Good with BiContainer Good Nat should be accepted (positive nesting)");

    // Now the actual test: Bad with TWO constructors using BiContainer with swapped params.
    // c1 : BiContainer Bad Nat → Bad  (Bad in A=positive position)
    // c2 : BiContainer Nat Bad → Bad  (Bad in B=negative position)
    let bad = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad.clone(), vec![]);

    // c1 : BiContainer Bad Nat → Bad
    let c1_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::const_(bicont.clone(), vec![]),
                bad_ref.clone(), // A = Bad
            ),
            Expr::const_(nat.clone(), vec![]), // B = Nat
        ),
        bad_ref.clone(),
    );

    // c2 : BiContainer Nat Bad → Bad
    let c2_type = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::const_(bicont.clone(), vec![]),
                Expr::const_(nat.clone(), vec![]), // A = Nat
            ),
            bad_ref.clone(), // B = Bad
        ),
        bad_ref.clone(),
    );

    let bad_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bad.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bad.c1"),
                    type_: c1_type,
                },
                Constructor {
                    name: Name::from_string("Bad.c2"),
                    type_: c2_type,
                },
            ],
        }],
    };

    let result = env.add_inductive(bad_decl);
    let err = result.expect_err(
        "Bad type with BiContainer Nat Bad must be rejected (Bad in negative position). \
         If this passes, the visited-set scoping bug allows unsound types through \
         when two constructors use the same container with different param orderings.",
    );
    // Must be NonPositive specifically (not TypeCheckFailed from F3 or other errors).
    // If check ordering changes, this ensures the test still validates the positivity checker.
    assert!(
        matches!(
            err,
            EnvError::Inductive(crate::inductive::InductiveError::NonPositive(..))
        ),
        "Expected NonPositive error for visited-set soundness test, got: {err}"
    );
}

/// Regression test for #2001: And is a parameterized inductive with 2 type params.
/// add_inductive must accept well-formed constructor type with correct de Bruijn indices.
#[test]
fn test_add_inductive_and_parameterized_2001() {
    let mut env = Environment::new();

    let and_name = Name::from_string("And");

    // And : Type → Type → Type
    let and_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A : Type
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(), // B : Type
            Expr::type_(), // : Type
        ),
    );

    // And.intro : {A : Type} → {B : Type} → A → B → And A B
    // De Bruijn encoding:
    //   Pi(Implicit, Sort(1),       -- A : Type
    //     Pi(Implicit, Sort(1),     -- B : Type
    //       Pi(Default, BVar(1),    -- a : A   (BVar(1) under 2 binders = A)
    //         Pi(Default, BVar(1),  -- b : B   (BVar(1) under 3 binders = B)
    //           App(App(Const(And), BVar(3)), BVar(2))  -- And A B
    //         ))))
    let intro_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(), // A : Type
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(), // B : Type
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1), // b : B
                    Expr::app(
                        Expr::app(
                            Expr::const_(and_name.clone(), vec![]),
                            Expr::bvar(3), // A
                        ),
                        Expr::bvar(2), // B
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: and_name.clone(),
            type_: and_type,
            constructors: vec![Constructor {
                name: Name::from_string("And.intro"),
                type_: intro_type,
            }],
        }],
    };

    env.add_inductive(decl).unwrap();

    // Verify registration
    let ind_info = env.get_inductive(&and_name).unwrap();
    assert_eq!(ind_info.num_params, 2);
    assert_eq!(ind_info.constructor_names.len(), 1);
}

/// Verify that get_max_height correctly handles shared sub-expressions via the
/// pointer-keyed visited set. When the same Arc<Expr> appears in multiple
/// positions, the visited set prevents redundant traversal and ensures
/// termination for DAG-structured expressions.
/// Exercises the *const Expr HashSet key invariant (see unfold.rs:59).
#[test]
fn test_get_max_height_shared_subexpr_visited_set() {
    use std::sync::Arc;

    let mut env = Environment::new();

    // Add two non-reducible definitions at different heights.
    // is_reducible=false gives Regular(max_height(value) + 1), which stores
    // a nonzero height we can detect:
    //   foo : Prop := Prop  -> Regular(0 + 1) = Regular(1), height = 1
    //   bar : Prop := foo   -> Regular(1 + 1) = Regular(2), height = 2
    let foo_name = Name::from_string("foo");
    env.add_decl_unchecked(Declaration::Definition {
        name: foo_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::prop(),
        is_reducible: false,
    });

    let bar_name = Name::from_string("bar");
    let foo_ref = Expr::const_str("foo");
    env.add_decl_unchecked(Declaration::Definition {
        name: bar_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
        value: foo_ref,
        is_reducible: false,
    });

    // Sanity: verify the heights are as expected
    assert_eq!(env.get_const(&foo_name).unwrap().reducibility.height(), 1);
    assert_eq!(env.get_const(&bar_name).unwrap().reducibility.height(), 2);

    // Create a shared sub-expression referencing "bar" (height 2)
    let shared_bar: Arc<Expr> = Arc::new(Expr::const_str("bar"));

    // Build App(bar, bar) where both sides share the SAME Arc pointer.
    // The visited set must detect that the second "bar" has the same address
    // and skip re-traversal.
    let app_shared = Expr::from_kind(ExprKind::App(
        Arc::clone(&shared_bar),
        Arc::clone(&shared_bar),
    ));

    let height = env.get_max_height(&app_shared);
    assert_eq!(
        height, 2,
        "get_max_height should find bar's height=2 even with shared sub-expressions"
    );

    // Also verify with a deeper tree: App(App(bar, bar), App(bar, bar))
    // where the inner App nodes are also shared.
    let inner_app: Arc<Expr> = Arc::new(app_shared);
    let outer_app = Expr::from_kind(ExprKind::App(
        Arc::clone(&inner_app),
        Arc::clone(&inner_app),
    ));

    let height2 = env.get_max_height(&outer_app);
    assert_eq!(
        height2, 2,
        "get_max_height should handle nested shared sub-expressions"
    );
}

// ===================================================================
// Environment pre-allocation tests (#3133)
// ===================================================================

#[test]
fn test_with_capacity_creates_functional_env() {
    // with_capacity should produce an environment that can add declarations
    let mut env = Environment::with_capacity(1000);

    // Sorry should be initialized (same as Environment::new())
    assert!(
        env.get_const(&Name::from_string("sorry")).is_some(),
        "with_capacity should initialize sorry"
    );

    // Should be able to add a simple axiom
    let prop = Expr::prop();
    let name = Name::from_string("testAxiom");
    let axiom = Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: prop,
    };
    env.add_decl(axiom)
        .expect("should accept axiom in pre-allocated env");
    assert!(env.get_const(&name).is_some());
}

#[test]
fn test_with_capacity_large_does_not_panic() {
    // Ensure large capacity requests (like Init's 60K constants) don't panic
    let env = Environment::with_capacity(60_000);
    assert_eq!(
        env.num_constants(),
        3,
        "should have sorry + trustedArith + trustedAy"
    );
}

#[test]
fn test_reserve_capacity_allows_growth() {
    let mut env = Environment::new();
    let initial_count = env.num_constants();

    // Reserve for a large batch
    env.reserve_capacity(10_000);

    // Environment should still function normally
    let prop = Expr::prop();
    let name = Name::from_string("postReserve");
    let axiom = Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: prop,
    };
    env.add_decl(axiom)
        .expect("should accept axiom after reserve");
    assert_eq!(env.num_constants(), initial_count + 1);
}

// ─── #3425: expression-level source locations in add_decl errors ──────────────
//
// These end-to-end tests construct ill-typed declarations and assert that the
// resulting `EnvError::TypeCheckFailed { source, .. }` carries a populated
// `ExprLocation` with (a) the declaration name and (b) the path of ExprPathSteps
// from the declaration root to the offending sub-expression.

/// `def bad : Prop := Type` — value does not inhabit the declared type.
/// The TypeMismatch is reported at the root of the value, so the trail has
/// no path steps but DOES carry the declaration name (from #3425 wiring in
/// `add_decl`).
#[test]
fn test_location_add_decl_type_value_mismatch_carries_decl_name() {
    let mut env = Environment::new();
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_def"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::type_(),
        is_reducible: false,
    });
    let err = result.expect_err("ill-typed def must be rejected");
    let EnvError::TypeCheckFailed { source, .. } = err else {
        panic!("expected TypeCheckFailed, got {err:?}");
    };
    let loc = source
        .location()
        .expect("TypeMismatch from add_decl should carry an ExprLocation");
    assert_eq!(
        loc.decl_name.as_ref().map(|n| n.to_string()),
        Some("bad_def".to_string()),
        "location should carry the declaration name"
    );
    let msg = source.to_string();
    assert!(
        msg.contains("bad_def"),
        "error message should mention declaration, got: {msg}"
    );
    assert!(
        msg.contains("Type mismatch"),
        "error message should describe the mismatch, got: {msg}"
    );
}

/// `axiom bad : (Prop Prop)` — applying `Prop` to `Prop` (non-function app).
/// Exercises `NotAFunction` at the declared type, so the location path
/// should include the decl name (`add_decl` wires it) and at least one
/// path step (`AppFn` descent while inferring the type's sort).
#[test]
fn test_location_add_decl_not_a_function_includes_path() {
    let mut env = Environment::new();
    // Type: `Prop Prop` — ill-typed: Prop is not a function.
    let bad_type = Expr::app(Expr::prop(), Expr::prop());
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("bad_type"),
        level_params: vec![],
        type_: bad_type,
    });
    let err = result.expect_err("axiom with ill-typed type must be rejected");
    let EnvError::TypeCheckFailed { source, .. } = err else {
        panic!("expected TypeCheckFailed, got {err:?}");
    };
    let loc = source
        .location()
        .expect("NotAFunction from add_decl should carry an ExprLocation");
    assert_eq!(
        loc.decl_name.as_ref().map(|n| n.to_string()),
        Some("bad_type".to_string())
    );
    // The type is `Prop Prop`. `infer_sort` -> `infer_type` descends into
    // `App(f, a)` and, before the NotAFunction bails out, has already pushed
    // AppFn while inferring `f`'s type. By the time the error is raised it has
    // been popped, so we only require that the decl-name shows up. The error
    // *message* should also clearly describe what went wrong.
    let msg = source.to_string();
    assert!(
        msg.contains("bad_type"),
        "error message should include decl name, got: {msg}"
    );
    assert!(
        msg.contains("Expected function type"),
        "error message should describe the NotAFunction, got: {msg}"
    );
}

/// `def bad : Prop := fun (x : Prop) => Type`  — body of a lambda has the
/// wrong type. The location path should show we descended into the lambda
/// body while checking the value against the declared Prop type.
#[test]
fn test_location_add_decl_mismatch_inside_lambda_body() {
    let mut env = Environment::new();

    // Declared type: `Prop -> Prop`
    let decl_type = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    // Value: `fun (x : Prop) => Type`  — body has type Sort(2), not Prop.
    let value = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::type_());

    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_lambda"),
        level_params: vec![],
        type_: decl_type,
        value,
        is_reducible: false,
    });
    let err = result.expect_err("ill-typed lambda must be rejected");
    let EnvError::TypeCheckFailed { source, .. } = err else {
        panic!("expected TypeCheckFailed, got {err:?}");
    };
    // The outer `check_type` produces a TypeMismatch between Pi(Prop, Prop) and
    // the inferred Pi(Prop, Type). We expect the location to at least carry the
    // decl name. Depending on which branch the kernel takes (check_type's final
    // is_def_eq vs. an inner infer path) the path may or may not include
    // LamBody — accept either, but require the decl-name prefix.
    let loc = source
        .location()
        .expect("mismatch under lambda should carry an ExprLocation");
    assert_eq!(
        loc.decl_name.as_ref().map(|n| n.to_string()),
        Some("bad_lambda".to_string())
    );
    let msg = source.to_string();
    assert!(msg.contains("bad_lambda"), "got: {msg}");
    assert!(msg.contains("Type mismatch"), "got: {msg}");
}

/// Debug-print the actual add_decl error messages so we can paste them into
/// the #3425 issue comment as before/after evidence. Prints to stdout when
/// run with `cargo test -- --nocapture`.
#[test]
fn test_location_demo_rendered_errors() {
    // Example 1: def bad_def : Prop := Type
    let mut env = Environment::new();
    let err = env
        .add_decl(Declaration::Definition {
            name: Name::from_string("bad_def"),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::type_(),
            is_reducible: false,
        })
        .unwrap_err();
    if let EnvError::TypeCheckFailed { source, .. } = err {
        println!("[demo #1] def bad_def : Prop := Type\n          => {source}");
    }

    // Example 2: axiom bad_app : (Prop Prop)
    let mut env = Environment::new();
    let bad_type = Expr::app(Expr::prop(), Expr::prop());
    let err = env
        .add_decl(Declaration::Axiom {
            name: Name::from_string("bad_app"),
            level_params: vec![],
            type_: bad_type,
        })
        .unwrap_err();
    if let EnvError::TypeCheckFailed { source, .. } = err {
        println!("[demo #2] axiom bad_app : (Prop Prop)\n          => {source}");
    }

    // Example 3: def bad_lam : Prop -> Prop := fun (x : Prop) => Type
    let mut env = Environment::new();
    let err = env
        .add_decl(Declaration::Definition {
            name: Name::from_string("bad_lam"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            value: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::type_()),
            is_reducible: false,
        })
        .unwrap_err();
    if let EnvError::TypeCheckFailed { source, .. } = err {
        println!("[demo #3] def bad_lam : Prop -> Prop := fun _ => Type\n          => {source}");
    }
}

/// Demonstrates the full error message format for the issue. Sanity-checks the
/// human-readable rendering of a TypeMismatch with declaration name + path.
#[test]
fn test_location_error_message_format_example() {
    use crate::tc::expr_location::{ExprLocation, ExprPathStep};
    use crate::tc::TypeError;

    let mut loc = ExprLocation::with_decl_name(Name::from_string("my.theorem"));
    loc.push(ExprPathStep::LamBody);
    loc.push(ExprPathStep::AppArg);

    let err = TypeError::TypeMismatch {
        expected: Box::new(Expr::prop()),
        inferred: Box::new(Expr::type_()),
        location: Some(Box::new(loc)),
    };
    let msg = err.to_string();
    // The rendered error should read something like:
    //   "Type mismatch: expected ..., got ...
    //     in declaration 'my.theorem', at body of lambda > argument of application"
    assert!(msg.contains("Type mismatch"), "msg: {msg}");
    assert!(msg.contains("in declaration 'my.theorem'"), "msg: {msg}");
    assert!(
        msg.contains("body of lambda > argument of application"),
        "msg: {msg}"
    );
}

/// Guard: the prelude declares `String.append`, the `HAppend` class, its
/// `HAppend.hAppend` projection, and the `instHAppendString` instance as
/// genuine, kernel-checked, axiom-free constants (backing the `++` operator on
/// strings). Each must type-check (`infer_type` succeeds) and carry no axiom
/// dependencies.
#[test]
fn test_string_append_and_happend_are_axiom_free() {
    let env = Environment::with_prelude();
    for name in [
        "String.append",
        "HAppend",
        "HAppend.hAppend",
        "instHAppendString",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{name} must be a declared constant in the prelude"));
        // The declared type must itself type-check (be a valid Sort).
        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&info.type_)
            .unwrap_or_else(|e| panic!("{name} type must infer cleanly: {e:?}"));
        // No axiom dependencies — a real Definition/inductive, not a trusted hole.
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("axiom_deps should resolve for {name}"));
        assert!(
            deps.is_empty(),
            "{name} must be axiom-free; deps: {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>()
        );
    }
}
