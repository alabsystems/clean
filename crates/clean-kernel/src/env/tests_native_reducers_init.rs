// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Init-specific native reducers (native_reducers_init.rs).
//!
//! Part of #3210: reduce heartbeat usage for Init .olean type-checking.

use crate::env::native_reducers_init::names;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;

// --- Helper constructors ---

/// `Decidable.isTrue p h` — the SATURATED constructor: inductive parameter `p`
/// (the proposition) followed by the proof field `h : p`. Real Lean terms always
/// carry both, so the proof is the LAST argument, not the first.
fn mk_decidable_is_true(prop: Expr, proof: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
            prop,
        ),
        proof,
    )
}

/// `Decidable.isFalse p h` — saturated `isFalse` constructor (`p` then `h : ¬p`).
fn mk_decidable_is_false(prop: Expr, proof: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
            prop,
        ),
        proof,
    )
}

fn mk_sorry() -> Expr {
    Expr::const_(Name::from_string("sorryAx"), vec![])
}

fn mk_list_nil() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    )
}

fn mk_list_cons(elem: Expr, tail: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("List.cons"), vec![]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            elem,
        ),
        tail,
    )
}

fn mk_array_mk(list: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Array.mk"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
        list,
    )
}

// --- ite tests ---

#[test]
fn test_ite_true_branch() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::ITE)
        .expect("ite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let cond = Expr::const_(Name::from_string("someProp"), vec![]);
    let inst = mk_decidable_is_true(cond.clone(), mk_sorry());
    let then_val = Expr::nat_lit(42);
    let else_val = Expr::nat_lit(0);

    let result = reducer(&[&alpha, &cond, &inst, &then_val, &else_val]);
    assert!(result.is_some(), "ite with isTrue should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(42), "Should select then branch");
    } else {
        panic!("Expected Nat literal 42");
    }
}

#[test]
fn test_ite_false_branch() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::ITE)
        .expect("ite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let cond = Expr::const_(Name::from_string("someProp"), vec![]);
    let inst = mk_decidable_is_false(cond.clone(), mk_sorry());
    let then_val = Expr::nat_lit(42);
    let else_val = Expr::nat_lit(0);

    let result = reducer(&[&alpha, &cond, &inst, &then_val, &else_val]);
    assert!(result.is_some(), "ite with isFalse should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(0), "Should select else branch");
    } else {
        panic!("Expected Nat literal 0");
    }
}

#[test]
fn test_ite_non_concrete_returns_none() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::ITE)
        .expect("ite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let cond = Expr::const_(Name::from_string("someProp"), vec![]);
    // Non-concrete Decidable instance (just a variable)
    let inst = Expr::const_(Name::from_string("someInst"), vec![]);
    let then_val = Expr::nat_lit(42);
    let else_val = Expr::nat_lit(0);

    let result = reducer(&[&alpha, &cond, &inst, &then_val, &else_val]);
    assert!(
        result.is_none(),
        "Non-concrete Decidable should return None"
    );
}

#[test]
fn test_ite_insufficient_args() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::ITE)
        .expect("ite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let cond = Expr::const_(Name::from_string("someProp"), vec![]);
    let inst = mk_decidable_is_true(cond.clone(), mk_sorry());

    let result = reducer(&[&alpha, &cond, &inst]);
    assert!(result.is_none(), "Insufficient args should return None");
}

// --- dite tests ---

#[test]
fn test_dite_true_branch() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::DITE)
        .expect("dite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let cond = Expr::const_(Name::from_string("someProp"), vec![]);
    let proof = mk_sorry();
    let inst = mk_decidable_is_true(cond.clone(), proof.clone());
    // then_fn and else_fn are functions that take a proof
    let then_fn = Expr::const_(Name::from_string("thenBranch"), vec![]);
    let else_fn = Expr::const_(Name::from_string("elseBranch"), vec![]);

    let result = reducer(&[&alpha, &cond, &inst, &then_fn, &else_fn]);
    assert!(result.is_some(), "dite with isTrue should reduce");
    // Result should be App(thenBranch, proof)
    let result = result.unwrap();
    if let ExprKind::App(f, arg) = result.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            assert_eq!(*name, Name::from_string("thenBranch"));
        } else {
            panic!("Expected thenBranch function");
        }
        // arg should be the proof (sorryAx)
        if let ExprKind::Const(name, _) = arg.kind() {
            assert_eq!(*name, Name::from_string("sorryAx"));
        } else {
            panic!("Expected sorryAx proof");
        }
    } else {
        panic!("Expected App(thenBranch, proof)");
    }
}

#[test]
fn test_dite_false_branch() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::DITE)
        .expect("dite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let cond = Expr::const_(Name::from_string("someProp"), vec![]);
    let proof = mk_sorry();
    let inst = mk_decidable_is_false(cond.clone(), proof.clone());
    let then_fn = Expr::const_(Name::from_string("thenBranch"), vec![]);
    let else_fn = Expr::const_(Name::from_string("elseBranch"), vec![]);

    let result = reducer(&[&alpha, &cond, &inst, &then_fn, &else_fn]);
    assert!(result.is_some(), "dite with isFalse should reduce");
    let result = result.unwrap();
    if let ExprKind::App(f, _) = result.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            assert_eq!(*name, Name::from_string("elseBranch"));
        } else {
            panic!("Expected elseBranch function");
        }
    } else {
        panic!("Expected App(elseBranch, proof)");
    }
}

// --- dite proof-field selection (WS9 regression) ---

/// Regression for the WS9 `dif_pos`/`dif_neg`/`instDecidableDite` family.
///
/// `Decidable.isTrue` is `(p : Prop) → p → Decidable p`, so a saturated value
/// `Decidable.isTrue p h` has the argument spine `[p, h]`. The native `dite`
/// reducer must apply the then-branch to the PROOF FIELD `h` (`args[1]`), not
/// the inductive PARAMETER `p` (`args[0]`). The old code took `args.first()`,
/// reducing `dite p (isTrue p h) t e` to `t p` instead of `t h` — which then
/// failed to match the lemma's stated `t h` type.
#[test]
fn test_dite_selects_proof_field_not_parameter() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::DITE)
        .expect("dite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    // distinct param vs proof so we can tell which one the reducer selected
    let prop = Expr::const_(Name::from_string("theProp"), vec![]);
    let proof = Expr::const_(Name::from_string("theProof"), vec![]);
    let inst = mk_decidable_is_true(prop.clone(), proof.clone());
    let then_fn = Expr::const_(Name::from_string("thenBranch"), vec![]);
    let else_fn = Expr::const_(Name::from_string("elseBranch"), vec![]);

    let result = reducer(&[&alpha, &prop, &inst, &then_fn, &else_fn])
        .expect("saturated isTrue should reduce");
    // Must be App(thenBranch, theProof) — NOT App(thenBranch, theProp).
    let ExprKind::App(f, arg) = result.kind() else {
        panic!("expected App(thenBranch, proof)");
    };
    assert!(
        matches!(f.kind(), ExprKind::Const(n, _) if *n == Name::from_string("thenBranch")),
        "expected the then-branch to be selected"
    );
    assert!(
        matches!(arg.kind(), ExprKind::Const(n, _) if *n == Name::from_string("theProof")),
        "dite must apply the then-branch to the PROOF FIELD, not the parameter; got {:?}",
        arg.kind()
    );
}

/// Adversarial: an UNDER-applied `Decidable.isTrue p` (no proof field yet) must
/// NOT reduce. Selecting `args[0]` (the parameter `p`) as if it were the proof
/// would be unsound — it would let `dite p (isTrue p) t e` compute `t p`, a
/// term of the wrong type. The reducer must return `None` (stuck) so the
/// ordinary recursor machinery handles the value once it is saturated.
#[test]
fn test_dite_unsaturated_decidable_does_not_reduce() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::DITE)
        .expect("dite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::const_(Name::from_string("theProp"), vec![]);
    // isTrue applied to ONLY the parameter — the proof field is missing.
    let inst = Expr::app(
        Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
        prop.clone(),
    );
    let then_fn = Expr::const_(Name::from_string("thenBranch"), vec![]);
    let else_fn = Expr::const_(Name::from_string("elseBranch"), vec![]);

    let result = reducer(&[&alpha, &prop, &inst, &then_fn, &else_fn]);
    assert!(
        result.is_none(),
        "under-applied Decidable.isTrue must NOT reduce (would mis-select the parameter as a proof)"
    );
}

/// Adversarial: an over-applied / non-Decidable head must not reduce.
#[test]
fn test_dite_non_decidable_head_does_not_reduce() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::DITE)
        .expect("dite reducer should be registered");

    let alpha = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::const_(Name::from_string("theProp"), vec![]);
    // A two-arg application whose head is NOT a Decidable constructor.
    let inst = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("someOtherCtor"), vec![]),
            prop.clone(),
        ),
        Expr::const_(Name::from_string("x"), vec![]),
    );
    let then_fn = Expr::const_(Name::from_string("thenBranch"), vec![]);
    let else_fn = Expr::const_(Name::from_string("elseBranch"), vec![]);

    let result = reducer(&[&alpha, &prop, &inst, &then_fn, &else_fn]);
    assert!(
        result.is_none(),
        "dite over a non-Decidable head must not reduce"
    );
}

// --- Ord.compare tests ---

#[test]
fn test_ord_compare_nat_lt() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env
        .get_native_reducer(&names::ORD_COMPARE)
        .expect("Ord.compare reducer should be registered");

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    let result = reducer(&[&nat_type, &inst, &a, &b]);
    assert!(result.is_some(), "Ord.compare instOrdNat 3 5 should reduce");
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Ordering.lt"));
    } else {
        panic!("Expected Ordering.lt");
    }
}

#[test]
fn test_ord_compare_nat_eq() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::ORD_COMPARE).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let a = Expr::nat_lit(7);
    let b = Expr::nat_lit(7);

    let result = reducer(&[&nat_type, &inst, &a, &b]);
    assert!(result.is_some(), "Ord.compare instOrdNat 7 7 should reduce");
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Ordering.eq"));
    } else {
        panic!("Expected Ordering.eq");
    }
}

#[test]
fn test_ord_compare_nat_gt() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::ORD_COMPARE).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instOrdNat"), vec![]);
    let a = Expr::nat_lit(10);
    let b = Expr::nat_lit(3);

    let result = reducer(&[&nat_type, &inst, &a, &b]);
    assert!(
        result.is_some(),
        "Ord.compare instOrdNat 10 3 should reduce"
    );
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Ordering.gt"));
    } else {
        panic!("Expected Ordering.gt");
    }
}

#[test]
fn test_ord_compare_unknown_instance_returns_none() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::ORD_COMPARE).unwrap();

    let ty = Expr::const_(Name::from_string("MyType"), vec![]);
    let inst = Expr::const_(Name::from_string("instOrdMyType"), vec![]);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);

    let result = reducer(&[&ty, &inst, &a, &b]);
    assert!(result.is_none(), "Unknown Ord instance should return None");
}

// --- List.length tests ---

#[test]
fn test_list_length_empty() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::LIST_LENGTH).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let nil = mk_list_nil();

    let result = reducer(&[&nat_type, &nil]);
    assert!(result.is_some(), "List.length [] should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(0));
    } else {
        panic!("Expected Nat literal 0");
    }
}

#[test]
fn test_list_length_three_elements() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::LIST_LENGTH).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let list = mk_list_cons(
        Expr::nat_lit(1),
        mk_list_cons(
            Expr::nat_lit(2),
            mk_list_cons(Expr::nat_lit(3), mk_list_nil()),
        ),
    );

    let result = reducer(&[&nat_type, &list]);
    assert!(result.is_some(), "List.length [1,2,3] should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(3));
    } else {
        panic!("Expected Nat literal 3");
    }
}

#[test]
fn test_list_length_non_concrete_returns_none() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::LIST_LENGTH).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    // A non-concrete list (just a variable)
    let list = Expr::const_(Name::from_string("someList"), vec![]);

    let result = reducer(&[&nat_type, &list]);
    assert!(result.is_none(), "Non-concrete list should return None");
}

// --- List.getLast! tests ---

#[test]
fn test_list_get_last_singleton() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::LIST_GET_LAST_BANG).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instInhabitedNat"), vec![]);
    let list = mk_list_cons(Expr::nat_lit(42), mk_list_nil());

    let result = reducer(&[&nat_type, &inst, &list]);
    assert!(result.is_some(), "List.getLast! [42] should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(42));
    } else {
        panic!("Expected Nat literal 42");
    }
}

#[test]
fn test_list_get_last_multi() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::LIST_GET_LAST_BANG).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instInhabitedNat"), vec![]);
    let list = mk_list_cons(
        Expr::nat_lit(1),
        mk_list_cons(
            Expr::nat_lit(2),
            mk_list_cons(Expr::nat_lit(3), mk_list_nil()),
        ),
    );

    let result = reducer(&[&nat_type, &inst, &list]);
    assert!(result.is_some(), "List.getLast! [1,2,3] should reduce to 3");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(3));
    } else {
        panic!("Expected Nat literal 3");
    }
}

#[test]
fn test_list_get_last_empty_returns_none() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::LIST_GET_LAST_BANG).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instInhabitedNat"), vec![]);
    let nil = mk_list_nil();

    let result = reducer(&[&nat_type, &inst, &nil]);
    assert!(result.is_none(), "List.getLast! [] should return None");
}

// --- Array.size tests ---

#[test]
fn test_array_size_empty() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::ARRAY_SIZE).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let array = mk_array_mk(mk_list_nil());

    let result = reducer(&[&nat_type, &array]);
    assert!(result.is_some(), "Array.size #[] should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(0));
    } else {
        panic!("Expected Nat literal 0");
    }
}

#[test]
fn test_array_size_two_elements() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::ARRAY_SIZE).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let list = mk_list_cons(
        Expr::nat_lit(10),
        mk_list_cons(Expr::nat_lit(20), mk_list_nil()),
    );
    let array = mk_array_mk(list);

    let result = reducer(&[&nat_type, &array]);
    assert!(result.is_some(), "Array.size #[10,20] should reduce");
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(2));
    } else {
        panic!("Expected Nat literal 2");
    }
}

#[test]
fn test_array_size_non_array_returns_none() {
    let mut env = Environment::new();
    env.init_init_native_reducers();
    let reducer = env.get_native_reducer(&names::ARRAY_SIZE).unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let not_array = Expr::const_(Name::from_string("someArray"), vec![]);

    let result = reducer(&[&nat_type, &not_array]);
    assert!(result.is_none(), "Non-Array.mk value should return None");
}

// --- Registration test ---

#[test]
fn test_all_init_reducers_registered() {
    let mut env = Environment::new();
    env.init_init_native_reducers();

    assert!(
        env.get_native_reducer(&names::ITE).is_some(),
        "ite reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::DITE).is_some(),
        "dite reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::ORD_COMPARE).is_some(),
        "Ord.compare reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::COMPARE_OF_LESS_AND_EQ)
            .is_some(),
        "compareOfLessAndEq reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LIST_LENGTH).is_some(),
        "List.length reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::LIST_GET_LAST_BANG).is_some(),
        "List.getLast! reducer should be registered"
    );
    assert!(
        env.get_native_reducer(&names::ARRAY_SIZE).is_some(),
        "Array.size reducer should be registered"
    );
}

// --- Reduction cache tests ---

#[test]
fn test_reduction_cache_basic() {
    use crate::env::reduction_cache::ReductionCache;

    let mut cache = ReductionCache::new();
    assert!(cache.is_empty());

    let name = Name::from_string("test.constant");
    let value = Expr::nat_lit(42);
    cache.insert(name.clone(), value.clone());

    assert_eq!(cache.len(), 1);
    assert!(!cache.is_empty());
    assert!(cache.get(&name).is_some());
}

#[test]
fn test_reduction_cache_eviction() {
    use crate::env::reduction_cache::ReductionCache;

    let mut cache = ReductionCache::with_capacity(3);
    for i in 0..3 {
        cache.insert(
            Name::from_string(&format!("const_{}", i)),
            Expr::nat_lit(i as u64),
        );
    }
    assert_eq!(cache.len(), 3);

    // Inserting a 4th entry should trigger eviction (clear + insert)
    cache.insert(Name::from_string("const_3"), Expr::nat_lit(3));
    assert_eq!(cache.len(), 1);
    assert!(cache.get(&Name::from_string("const_3")).is_some());
    assert!(cache.get(&Name::from_string("const_0")).is_none());
}

#[test]
fn test_reduction_cache_zero_capacity() {
    use crate::env::reduction_cache::ReductionCache;

    let mut cache = ReductionCache::with_capacity(0);
    cache.insert(Name::from_string("test"), Expr::nat_lit(1));
    assert!(cache.is_empty(), "Zero-capacity cache should never store");
}

#[test]
fn test_reduction_cache_clear() {
    use crate::env::reduction_cache::ReductionCache;

    let mut cache = ReductionCache::new();
    cache.insert(Name::from_string("a"), Expr::nat_lit(1));
    cache.insert(Name::from_string("b"), Expr::nat_lit(2));
    assert_eq!(cache.len(), 2);

    cache.clear();
    assert!(cache.is_empty());
    assert!(cache.get(&Name::from_string("a")).is_none());
}
