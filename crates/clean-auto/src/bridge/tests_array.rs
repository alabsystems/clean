// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for array theory translation: select/store operations, Lean 4 style
//! Array.get/Array.set mapping, and read-over-write structural verification.
//!
//! Extracted from bridge/tests.rs as part of Phase A test migration (#307).

use super::super::*;
use super::test_helpers::setup_env;

#[test]
fn test_array_select_translation() {
    // Test that Array.get expressions are translated to select terms
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let arr = Expr::const_(Name::from_string("arr"), vec![]);
    let idx = Expr::const_(Name::from_string("idx"), vec![]);

    // select(arr, idx) - direct array theory operation
    let select_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("select"), vec![]),
            arr.clone(),
        ),
        idx.clone(),
    );

    let select_tid = bridge
        .translate_term(&select_expr)
        .expect("translate select");

    // The compound select(arr, idx) must differ from its sub-terms
    let arr_tid = bridge.translate_term(&arr).expect("translate arr");
    let idx_tid = bridge.translate_term(&idx).expect("translate idx");
    assert_ne!(
        select_tid, arr_tid,
        "select(arr, idx) should differ from arr"
    );
    assert_ne!(
        select_tid, idx_tid,
        "select(arr, idx) should differ from idx"
    );

    // Verify the SMT term is actually a select operation, not a generic application
    let smt_term = bridge
        .smt
        .get_term(select_tid)
        .expect("select term should exist");
    match smt_term {
        crate::smt::SmtTerm::App(sym, args) => {
            assert_eq!(
                sym.name(),
                "select",
                "select(arr, idx) should translate to SMT select operation, got {sym:?}"
            );
            assert_eq!(
                args.len(),
                2,
                "SMT select should have 2 args (array, index), got {}",
                args.len()
            );
            assert_eq!(args[0], arr_tid, "select first arg should be arr");
            assert_eq!(args[1], idx_tid, "select second arg should be idx");
        }
        other => panic!("select(arr, idx) should translate to SmtTerm::App, got {other:?}"),
    }
}

#[test]
fn test_array_store_translation() {
    // Test that Array.set expressions are translated to store terms
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let arr = Expr::const_(Name::from_string("arr"), vec![]);
    let idx = Expr::const_(Name::from_string("idx"), vec![]);
    let val = Expr::const_(Name::from_string("val"), vec![]);

    // store(arr, idx, val) - direct array theory operation
    let store_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("store"), vec![]),
                arr.clone(),
            ),
            idx.clone(),
        ),
        val.clone(),
    );

    let store_tid = bridge.translate_term(&store_expr).expect("translate store");

    // The compound store(arr, idx, val) must differ from its sub-terms
    let arr_tid = bridge.translate_term(&arr).expect("translate arr");
    let idx_tid = bridge.translate_term(&idx).expect("translate idx");
    let val_tid = bridge.translate_term(&val).expect("translate val");
    assert_ne!(
        store_tid, arr_tid,
        "store(arr, idx, val) should differ from arr"
    );
    assert_ne!(
        store_tid, idx_tid,
        "store(arr, idx, val) should differ from idx"
    );
    assert_ne!(
        store_tid, val_tid,
        "store(arr, idx, val) should differ from val"
    );

    // Verify the SMT term is actually a store operation, not a generic application
    let smt_term = bridge
        .smt
        .get_term(store_tid)
        .expect("store term should exist");
    match smt_term {
        crate::smt::SmtTerm::App(sym, args) => {
            assert_eq!(
                sym.name(),
                "store",
                "store(arr, idx, val) should translate to SMT store operation, got {sym:?}"
            );
            assert_eq!(
                args.len(),
                3,
                "SMT store should have 3 args (array, index, value), got {}",
                args.len()
            );
            assert_eq!(args[0], arr_tid, "store first arg should be arr");
            assert_eq!(args[1], idx_tid, "store second arg should be idx");
            assert_eq!(args[2], val_tid, "store third arg should be val");
        }
        other => panic!("store(arr, idx, val) should translate to SmtTerm::App, got {other:?}"),
    }
}

#[test]
fn test_array_read_over_write_same_index() {
    // Test the array axiom: select(store(a, i, v), i) = v
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let arr = Expr::const_(Name::from_string("arr"), vec![]);
    let idx = Expr::const_(Name::from_string("i"), vec![]);
    let val = Expr::const_(Name::from_string("v"), vec![]);

    // store(arr, i, v)
    let store_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("store"), vec![]),
                arr.clone(),
            ),
            idx.clone(),
        ),
        val.clone(),
    );

    // select(store(arr, i, v), i)
    let select_store_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("select"), vec![]),
            store_expr,
        ),
        idx.clone(),
    );

    let lhs = bridge
        .translate_term(&select_store_expr)
        .expect("translate LHS");
    let rhs = bridge.translate_term(&val).expect("translate RHS");
    // At translation time, select(store(a,i,v),i) and v are structurally different terms.
    // The read-over-write axiom (select(store(a,i,v),i) = v) is applied later by the
    // array theory solver, not at translation time.
    assert_ne!(
        lhs, rhs,
        "select(store(a,i,v),i) and v should be distinct term IDs before axiom application"
    );

    // Verify the outer term is a select whose first arg is a store
    let outer = bridge
        .smt
        .get_term(lhs)
        .expect("select(store(...)) should exist");
    match outer {
        crate::smt::SmtTerm::App(sym, args) => {
            assert_eq!(sym.name(), "select", "Outer operation should be select");
            assert_eq!(args.len(), 2, "select should have 2 args");
            // First arg of select should be the store term
            let inner = bridge
                .smt
                .get_term(args[0])
                .expect("store term should exist");
            match inner {
                crate::smt::SmtTerm::App(inner_sym, inner_args) => {
                    assert_eq!(inner_sym.name(), "store", "Inner operation should be store");
                    assert_eq!(inner_args.len(), 3, "store should have 3 args");
                }
                other => panic!("First arg of select should be store App, got {other:?}"),
            }
        }
        other => panic!("select(store(...)) should be SmtTerm::App, got {other:?}"),
    }
}

#[test]
fn test_array_lean_style_get_translation() {
    // Test that Array.get (Lean 4 style) is translated correctly
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let arr = Expr::const_(Name::from_string("arr"), vec![]);
    let idx = Expr::const_(Name::from_string("idx"), vec![]);
    let ty_arg = Expr::const_(Name::from_string("Int"), vec![]);

    // Array.get α arr idx (with type argument)
    let array_get_expr = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Array.get"), vec![]), ty_arg),
            arr.clone(),
        ),
        idx.clone(),
    );

    let get_tid = bridge
        .translate_term(&array_get_expr)
        .expect("translate Array.get");

    // Array.get(α, arr, idx) must differ from its data sub-terms
    let arr_tid = bridge.translate_term(&arr).expect("translate arr");
    let idx_tid = bridge.translate_term(&idx).expect("translate idx");
    assert_ne!(
        get_tid, arr_tid,
        "Array.get(α, arr, idx) should differ from arr"
    );
    assert_ne!(
        get_tid, idx_tid,
        "Array.get(α, arr, idx) should differ from idx"
    );

    // Verify Array.get is translated to an SMT select operation (not a generic application)
    let smt_term = bridge
        .smt
        .get_term(get_tid)
        .expect("Array.get term should exist");
    match smt_term {
        crate::smt::SmtTerm::App(sym, args) => {
            assert_eq!(
                sym.name(),
                "select",
                "Array.get should map to SMT select, got {sym:?}"
            );
            assert_eq!(
                args.len(),
                2,
                "SMT select from Array.get should have 2 args (array, index), got {}",
                args.len()
            );
            assert_eq!(args[0], arr_tid, "Array.get select first arg should be arr");
            assert_eq!(
                args[1], idx_tid,
                "Array.get select second arg should be idx"
            );
        }
        other => {
            panic!("Array.get should translate to SmtTerm::App(\"select\", ..), got {other:?}")
        }
    }
}

#[test]
fn test_array_lean_style_set_translation() {
    // Test that Array.set (Lean 4 style) is translated correctly
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let arr = Expr::const_(Name::from_string("arr"), vec![]);
    let idx = Expr::const_(Name::from_string("idx"), vec![]);
    let val = Expr::const_(Name::from_string("val"), vec![]);
    let ty_arg = Expr::const_(Name::from_string("Int"), vec![]);

    // Array.set α arr idx val (with type argument)
    let array_set_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Array.set"), vec![]), ty_arg),
                arr.clone(),
            ),
            idx.clone(),
        ),
        val.clone(),
    );

    let set_tid = bridge
        .translate_term(&array_set_expr)
        .expect("translate Array.set");

    // Array.set(α, arr, idx, val) must differ from its data sub-terms
    let arr_tid = bridge.translate_term(&arr).expect("translate arr");
    let idx_tid = bridge.translate_term(&idx).expect("translate idx");
    let val_tid = bridge.translate_term(&val).expect("translate val");
    assert_ne!(
        set_tid, arr_tid,
        "Array.set(α, arr, idx, val) should differ from arr"
    );
    assert_ne!(
        set_tid, idx_tid,
        "Array.set(α, arr, idx, val) should differ from idx"
    );
    assert_ne!(
        set_tid, val_tid,
        "Array.set(α, arr, idx, val) should differ from val"
    );

    // Verify Array.set is translated to an SMT store operation (not a generic application)
    let smt_term = bridge
        .smt
        .get_term(set_tid)
        .expect("Array.set term should exist");
    match smt_term {
        crate::smt::SmtTerm::App(sym, args) => {
            assert_eq!(
                sym.name(),
                "store",
                "Array.set should map to SMT store, got {sym:?}"
            );
            assert_eq!(
                args.len(),
                3,
                "SMT store from Array.set should have 3 args (array, index, value), got {}",
                args.len()
            );
            assert_eq!(args[0], arr_tid, "Array.set store first arg should be arr");
            assert_eq!(args[1], idx_tid, "Array.set store second arg should be idx");
            assert_eq!(args[2], val_tid, "Array.set store third arg should be val");
        }
        other => panic!("Array.set should translate to SmtTerm::App(\"store\", ..), got {other:?}"),
    }
}
