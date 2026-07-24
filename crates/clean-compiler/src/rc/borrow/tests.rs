// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{LetDecl, Param};
use clean_kernel::Expr;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn test_simple_identity_all_borrowed() {
    // def id (x : Nat) : Nat := return x
    // No consumption → x should be borrowed
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let borrow = infer_borrow_single(&decl);
    assert_eq!(borrow.params.len(), 1);
    assert_eq!(borrow.params[0], Ownership::Borrowed);
}

#[test]
fn test_projection_propagates_ownership() {
    // def proj (p : Pair) : Nat :=
    //   let _1 := Pair.fst p
    //   let _2 := Pair.mk _1 _1  // _1 consumed by ctor
    //   return _2
    // p should be owned because projection result is owned
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Proj {
                type_name: name("Pair"),
                idx: 0,
                structure: fvar(0),
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Pair.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let decl = Decl::new(
        name("proj"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("p"), nat_type())],
        code,
        false,
    );

    let borrow = infer_borrow_single(&decl);
    // p should be owned because _1 is consumed and came from p
    assert_eq!(borrow.params[0], Ownership::Owned);
}

#[test]
fn test_constructor_args_owned() {
    // def wrap (x : Nat) : Box Nat :=
    //   let _1 := Box.mk x  // x consumed
    //   return _1
    // x should be owned
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Box.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );

    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    let borrow = infer_borrow_single(&decl);
    assert_eq!(borrow.params[0], Ownership::Owned);
}

#[test]
fn test_fn_borrow_mark_owned() {
    let mut borrow = FnBorrow::all_borrowed(3);
    assert!(borrow.mark_owned(1));
    assert_eq!(borrow.params[1], Ownership::Owned);
    // Already owned, should return false
    assert!(!borrow.mark_owned(1));
}

#[test]
fn test_borrow_map_operations() {
    let mut map = BorrowMap::new();
    map.insert(name("foo"), FnBorrow::all_borrowed(2));

    assert!(
        map.get(&name("foo")).is_some(),
        "expected 'foo' in borrow map"
    );
    assert!(
        map.get(&name("bar")).is_none(),
        "expected 'bar' absent from borrow map, got: {:?}",
        map.get(&name("bar"))
    );

    assert!(map.mark_owned(&name("foo"), 0));
    assert_eq!(map.get(&name("foo")).unwrap().params[0], Ownership::Owned);
}

#[test]
fn test_mutual_recursion_ownership_propagation() {
    // Test that ownership propagates correctly through mutually recursive functions.
    //
    // def even (x : Nat) : Nat :=
    //   let _1 := odd x    // calls odd with x
    //   return _1
    //
    // def odd (y : Nat) : Nat :=
    //   let _1 := Box.mk y  // y is consumed (owned)
    //   let _2 := even y    // also passes y to even
    //   return _2
    //
    // Since odd consumes y, and even passes x to odd, x should become owned.
    // This requires fixpoint iteration to propagate ownership through the cycle.

    // even: calls odd(x)
    let even_code = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: name("odd"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))], // pass x to odd
            },
        ),
        Code::ret(fvar(10)),
    );

    let even_decl = Decl::new(
        name("even"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        even_code,
        true, // recursive
    );

    // odd: consumes y in Box.mk, also calls even(y)
    let odd_code = Code::let_bind(
        LetDecl::new(
            fvar(20),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Box.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))], // consumes y
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(21),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("even"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))], // pass y to even
                },
            ),
            Code::ret(fvar(21)),
        ),
    );

    let odd_decl = Decl::new(
        name("odd"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("y"), nat_type())],
        odd_code,
        true, // recursive
    );

    // Run borrow inference on both declarations together
    let decls = vec![even_decl, odd_decl];
    let borrow_map = infer_borrow(&decls);

    // odd's y must be owned (consumed by Box.mk)
    let odd_borrow = borrow_map.get(&name("odd")).unwrap();
    assert_eq!(
        odd_borrow.params[0],
        Ownership::Owned,
        "odd's y should be owned (consumed by constructor)"
    );

    // even's x must be owned (passed to odd which requires ownership)
    let even_borrow = borrow_map.get(&name("even")).unwrap();
    assert_eq!(
        even_borrow.params[0],
        Ownership::Owned,
        "even's x should be owned (passed to odd which requires ownership)"
    );
}

#[test]
fn test_tail_call_reverse_direction_promotes_callee_param() {
    // Reverse tail-call promotion (Lean 4 ownParamsUsingArgs):
    // When a self-recursive tail call passes an owned arg at position i,
    // the function's param[i] must be Owned so the next invocation
    // can accept the ownership transfer.
    //
    // def f(x : Nat, y : Nat) : Nat :=
    //   let a := Box.mk x        -- x consumed, x is owned
    //   let b := f y x            -- self-recursive tail call, x at position 1
    //   return b
    //
    // Without reverse direction: param[0] (x) becomes Owned in iteration 1
    // (consumed by Ctor), and param[1] (y) eventually in iteration 2 (forward
    // propagation through the self-call). With reverse direction: param[1] (y)
    // is promoted to Owned in iteration 1 because arg[1] = x is already owned,
    // accelerating convergence. This exercises the promote_tail_call_owned path.

    // let a = Box.mk(x)
    // let b = f(y, x)   -- tail call with swapped args
    // return b
    let code = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("a"),
            nat_type(),
            LetValue::Ctor {
                name: name("Box.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))], // consumes x
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("b"),
                nat_type(),
                LetValue::Const {
                    name: name("f"), // self-recursive call
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(0))], // f(y, x)
                },
            ),
            Code::ret(fvar(11)), // return b — tail position
        ),
    );

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("x"), nat_type()),
            Param::new(fvar(1), name("y"), nat_type()),
        ],
        code,
        true, // recursive
    );

    let borrow = infer_borrow_single(&decl);

    // x is consumed by Box.mk → param[0] Owned (by collect_owned)
    assert_eq!(
        borrow.params[0],
        Ownership::Owned,
        "x should be owned (consumed by constructor)"
    );

    // At tail call f(y, x): arg[1] = x is owned → param[1] must be Owned
    // This is the reverse direction: owned arg promotes callee's param
    assert_eq!(
        borrow.params[1],
        Ownership::Owned,
        "y should be owned (reverse tail-call promotion: owned arg x at position 1)"
    );
}
