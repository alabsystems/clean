// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Positivity edge case tests: transitive nesting, is_valid_ind_app gaps,
// and Lean 4 reference comparison.
// Re: #2156 — soundness validation for nested positivity checking.

use crate::env::types::Declaration;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::name::Name;

fn env_with_nat() -> Environment {
    let mut env = Environment::new();
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    });
    env
}

/// Build a simple parametric inductive: `N (A : Type) : Type` with one ctor.
fn add_param_inductive(env: &mut Environment, name: &str, ctor_name: &str, ctor_type: Expr) {
    let n = Name::from_string(name);
    let ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: n,
            type_: ty,
            constructors: vec![Constructor {
                name: Name::from_string(ctor_name),
                type_: ctor_type,
            }],
        }],
    })
    .unwrap_or_else(|e| panic!("{name} must be valid: {e}"));
}

/// Build a simple non-param inductive with one ctor.
fn try_add_simple_inductive(
    env: &mut Environment,
    name: &str,
    ctor_name: &str,
    ctor_type: Expr,
) -> Result<(), crate::env::types::EnvError> {
    let n = Name::from_string(name);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(ctor_name),
                type_: ctor_type,
            }],
        }],
    })
}

/// NegContainer (X : Type) where mk : (X → Nat) → NegContainer X
fn neg_container_ctor_type(container: &Name, nat: &Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::arrow(Expr::bvar(0), nat.clone()),
            Expr::app(Expr::const_(container.clone(), vec![]), Expr::bvar(1)),
        ),
    )
}

/// Middle (Y : Type) where mk : Container Y → Middle Y
fn wrapper_ctor_type(container: &Name, wrapper: &Name) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(container.clone(), vec![]), Expr::bvar(0)),
            Expr::app(Expr::const_(wrapper.clone(), vec![]), Expr::bvar(1)),
        ),
    )
}

fn add_wrapper_chain(
    env: &mut Environment,
    base_container: &Name,
    prefix: &str,
    depth: usize,
) -> Name {
    let mut current = base_container.clone();
    for idx in 0..depth {
        let wrapper_name = format!("{prefix}{idx}");
        let wrapper = Name::from_string(&wrapper_name);
        add_param_inductive(
            env,
            &wrapper_name,
            &format!("{wrapper_name}.mk"),
            wrapper_ctor_type(&current, &wrapper),
        );
        current = wrapper;
    }
    current
}

// --- F1: Transitive nested positivity gap ---
// NegContainer (X) where mk : (X → Nat) → NegContainer X
// Middle (Y) where mk : NegContainer Y → Middle Y
// TransBad where mk : Middle TransBad → TransBad
// Bad appears negatively via NegContainer → Middle chain.
#[test]
fn test_transitive_nested_positivity_violation() {
    let mut env = env_with_nat();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nc = Name::from_string("NegContainer");
    let mid = Name::from_string("Middle");

    add_param_inductive(
        &mut env,
        "NegContainer",
        "NegContainer.mk",
        neg_container_ctor_type(&nc, &nat),
    );
    add_param_inductive(
        &mut env,
        "Middle",
        "Middle.mk",
        wrapper_ctor_type(&nc, &mid),
    );

    let bad_ref = Expr::const_(Name::from_string("TransBad"), vec![]);
    let mk_ty = Expr::arrow(
        Expr::app(Expr::const_(mid, vec![]), bad_ref.clone()),
        bad_ref,
    );
    let result = try_add_simple_inductive(&mut env, "TransBad", "TransBad.mk", mk_ty);

    // Fixed: check_through_container recursively calls check_nested_in_ctor_type
    // on instantiated Middle.mk, which sees NegContainer TransBad and recurses
    // into NegContainer's ctors where (TransBad → Nat) is correctly rejected.
    assert!(
        result.is_err(),
        "transitive nested negative occurrence must be rejected"
    );
}

#[test]
fn test_transitive_nested_positivity_rejected_across_wrapper_chain_depths() {
    // Multiple depths guard against regressions where recursive descent stops
    // after only one or two container hops.
    for depth in [1_usize, 2, 4, 8, 16] {
        let mut env = env_with_nat();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let neg_container = Name::from_string("NegContainer");
        add_param_inductive(
            &mut env,
            "NegContainer",
            "NegContainer.mk",
            neg_container_ctor_type(&neg_container, &nat),
        );

        let leaf_wrapper = add_wrapper_chain(&mut env, &neg_container, "NegWrap", depth);
        let bad_name = format!("TransBadDepth{depth}");
        let bad_ref = Expr::const_(Name::from_string(&bad_name), vec![]);
        let mk_ty = Expr::arrow(
            Expr::app(Expr::const_(leaf_wrapper, vec![]), bad_ref.clone()),
            bad_ref,
        );

        let result =
            try_add_simple_inductive(&mut env, &bad_name, &format!("{bad_name}.mk"), mk_ty);
        assert!(
            result.is_err(),
            "negative occurrence must be rejected through {depth} wrapper layers"
        );
    }
}

// --- F2: Constructor returning partially applied inductive ---
// Ind (A : Type) (B : Type) : Type
// Ind.mk : (A : Type) → (B : Type) → Ind A  (missing B!)
#[test]
fn test_recursive_occurrence_wrong_arity_rejected() {
    let mut env = env_with_nat();
    let ind = Name::from_string("Ind2P");
    let ind_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
    let ind_mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(Expr::const_(ind.clone(), vec![]), Expr::bvar(1)),
        ),
    );

    let result = env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: ind,
            type_: ind_type,
            constructors: vec![Constructor {
                name: Name::from_string("Ind2P.mk"),
                type_: ind_mk_type,
            }],
        }],
    });
    assert!(
        result.is_err(),
        "constructor returning partially applied inductive (wrong arity) must be rejected"
    );
}

// --- F3: Self-referencing index args (lean4#2125) ---
// BadRec2 : Type → Type where mk : (idx) → BadRec2 (BadRec2 idx) → BadRec2 idx
// Recursive arg BadRec2(BadRec2 idx) has BadRec2 in its index argument.
#[test]
fn test_inductive_in_index_args_rejected() {
    let mut env = env_with_nat();
    let br = Name::from_string("BadRec2");
    let br_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let br_mk = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(br.clone(), vec![]),
                Expr::app(Expr::const_(br.clone(), vec![]), Expr::bvar(0)),
            ),
            Expr::app(Expr::const_(br.clone(), vec![]), Expr::bvar(1)),
        ),
    );

    let result = env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: br,
            type_: br_type,
            constructors: vec![Constructor {
                name: Name::from_string("BadRec2.mk"),
                type_: br_mk,
            }],
        }],
    });

    // Covered by check_strictly_positive_impl: App head == BadRec2,
    // check_no_negative_occurrence on arg `BadRec2 idx` finds BadRec2 → Err.
    if result.is_ok() {
        panic!("inductive in index args accepted — missing lean4#2125 check");
    }
}

// --- F4: Double-nested positive container accepted ---
// PList (A) where nil | cons : A → PList A → PList A
// Wrap (B) where mk : PList B → Wrap B
// Good where mk : Wrap Good → Good
#[test]
fn test_double_nested_positive_accepted() {
    let mut env = env_with_nat();
    let pl = Name::from_string("PList");
    let nil_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(Expr::const_(pl.clone(), vec![]), Expr::bvar(0)),
    );
    let cons_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::const_(pl.clone(), vec![]), Expr::bvar(1)),
                Expr::app(Expr::const_(pl.clone(), vec![]), Expr::bvar(2)),
            ),
        ),
    );
    let plist_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: pl.clone(),
            type_: plist_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("PList.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("PList.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    })
    .expect("PList must be valid");

    let wrap = Name::from_string("Wrap");
    add_param_inductive(&mut env, "Wrap", "Wrap.mk", wrapper_ctor_type(&pl, &wrap));

    let good_ref = Expr::const_(Name::from_string("DoubleGood"), vec![]);
    let mk_ty = Expr::arrow(
        Expr::app(Expr::const_(wrap, vec![]), good_ref.clone()),
        good_ref,
    );
    let result = try_add_simple_inductive(&mut env, "DoubleGood", "DoubleGood.mk", mk_ty);
    assert!(
        result.is_ok(),
        "double-nested positive must be accepted: {:?}",
        result.err()
    );
}

#[test]
fn test_positive_nested_container_chain_accepted_across_wrapper_depths() {
    for depth in [1_usize, 2, 4, 8, 16] {
        let mut env = env_with_nat();
        let plist = Name::from_string("PList");
        let nil_ty = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(Expr::const_(plist.clone(), vec![]), Expr::bvar(0)),
        );
        let cons_ty = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::const_(plist.clone(), vec![]), Expr::bvar(1)),
                    Expr::app(Expr::const_(plist.clone(), vec![]), Expr::bvar(2)),
                ),
            ),
        );

        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: plist.clone(),
                type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("PList.nil"),
                        type_: nil_ty,
                    },
                    Constructor {
                        name: Name::from_string("PList.cons"),
                        type_: cons_ty,
                    },
                ],
            }],
        })
        .expect("PList must be valid");

        let leaf_wrapper = add_wrapper_chain(&mut env, &plist, "PosWrap", depth);
        let good_name = format!("DeepGoodDepth{depth}");
        let good_ref = Expr::const_(Name::from_string(&good_name), vec![]);
        let mk_ty = Expr::arrow(
            Expr::app(Expr::const_(leaf_wrapper, vec![]), good_ref.clone()),
            good_ref,
        );

        let result =
            try_add_simple_inductive(&mut env, &good_name, &format!("{good_name}.mk"), mk_ty);
        assert!(
            result.is_ok(),
            "positive occurrence must be accepted through {depth} wrapper layers: {:?}",
            result.err()
        );
    }
}
