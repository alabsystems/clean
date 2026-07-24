// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::Param;
use clean_kernel::{Expr, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn make_decl(n: &str, body: Code) -> Decl {
    Decl {
        name: name(n),
        level_params: vec![],
        ty: nat_type(),
        params: vec![Param::new(fvar(0), name("x"), nat_type())],
        body: DeclValue::Code(Box::new(body)),
        recursive: false,
    }
}

#[test]
fn test_map() {
    let items = vec![1, 2, 3];
    let result = map(&items, |x| x * 2);
    assert_eq!(result, vec![2, 4, 6]);
}

#[test]
fn test_filter() {
    let items = vec![1, 2, 3, 4, 5];
    let result = filter(&items, |x| x % 2 == 0);
    assert_eq!(result, vec![2, 4]);
}

#[test]
fn test_sorted() {
    let items = vec![3, 1, 4, 1, 5];
    let result = sorted(&items);
    assert_eq!(result, vec![1, 1, 3, 4, 5]);
}

#[test]
fn test_head() {
    let items = vec![1, 2, 3, 4, 5];
    assert_eq!(head(&items, 3), vec![1, 2, 3]);
    assert_eq!(head(&items, 10), vec![1, 2, 3, 4, 5]);
}

#[test]
fn test_tail() {
    let items = vec![1, 2, 3, 4, 5];
    assert_eq!(tail(&items, 3), vec![3, 4, 5]);
    assert_eq!(tail(&items, 10), vec![1, 2, 3, 4, 5]);
}

#[test]
fn test_count_unique() {
    let items = vec!["a", "b", "a", "c", "b", "a"];
    let counts = count_unique(&items);
    assert_eq!(counts.len(), 3);
    // Check that we have the right counts (order may vary)
    let a_count = counts.iter().find(|(k, _)| *k == "a").unwrap().1;
    let b_count = counts.iter().find(|(k, _)| *k == "b").unwrap().1;
    let c_count = counts.iter().find(|(k, _)| *k == "c").unwrap().1;
    assert_eq!(a_count, 3);
    assert_eq!(b_count, 2);
    assert_eq!(c_count, 1);
}

#[test]
fn test_count_unique_sorted() {
    let items = vec!["a", "b", "a", "c", "b", "a"];
    let counts = count_unique_sorted(&items);
    assert_eq!(counts.len(), 3);
    // Should be sorted by count ascending
    assert_eq!(counts[0].1, 1); // c appears once
    assert_eq!(counts[1].1, 2); // b appears twice
    assert_eq!(counts[2].1, 3); // a appears thrice
}

#[test]
fn test_code_size() {
    // Simple return
    let simple = make_decl("simple", Code::ret(fvar(0)));
    assert_eq!(code_size(&simple), 1);

    // Let binding + return
    let with_let = make_decl(
        "with_let",
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(1)),
        ),
    );
    assert_eq!(code_size(&with_let), 2);
}

#[test]
fn test_decl_names() {
    let decls = vec![
        make_decl("foo", Code::ret(fvar(0))),
        make_decl("bar", Code::ret(fvar(0))),
    ];
    let names = decl_names(&decls);
    assert_eq!(names, vec!["foo", "bar"]);
}

#[test]
fn test_get_let_values() {
    let decl = make_decl(
        "test",
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
            Code::let_bind(
                LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(100)),
                Code::ret(fvar(2)),
            ),
        ),
    );
    let values = get_let_values(&[decl]);
    assert_eq!(values.len(), 2);
}

#[test]
fn test_get_join_points() {
    let jp_decl = FunDecl {
        fvar_id: fvar(10),
        name: name("jp"),
        params: vec![],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(0))),
    };
    let decl = make_decl(
        "test",
        Code::JoinPoint(
            jp_decl,
            Box::new(Code::Jmp {
                jp: fvar(10),
                args: vec![],
            }),
        ),
    );
    let jps = get_join_points(&[decl]);
    assert_eq!(jps.len(), 1);
    assert_eq!(jps[0].fvar_id, fvar(10));
}

#[test]
fn test_filter_by_let() {
    let decl1 = make_decl(
        "has_nat",
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(1)),
        ),
    );
    let decl2 = make_decl("no_let", Code::ret(fvar(0)));

    let decls = vec![decl1, decl2];
    let filtered = filter_by_let(&decls, |let_decl| {
        matches!(&let_decl.value, LetValue::Lit(_))
    });

    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name.to_string(), "has_nat");
}

#[test]
fn test_filter_by_return() {
    let decl1 = make_decl("ret_0", Code::ret(fvar(0)));
    let decl2 = make_decl("ret_1", Code::ret(fvar(1)));

    let decls = vec![decl1, decl2];
    let filtered = filter_by_return(&decls, |fvar_id| fvar_id == fvar(0));

    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name.to_string(), "ret_0");
}

#[test]
fn test_filter_by_fun() {
    // Create a decl with a nested function
    let nested_fn = FunDecl {
        fvar_id: fvar(20),
        name: name("nested"),
        params: vec![Param::new(fvar(21), name("x"), nat_type())],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(21))),
    };
    let with_fun = make_decl(
        "has_fun",
        Code::Fun(nested_fn, Box::new(Code::ret(fvar(0)))),
    );
    let without_fun = make_decl("no_fun", Code::ret(fvar(0)));

    let decls = vec![with_fun, without_fun];
    let filtered = filter_by_fun(&decls, |fun| fun.params.len() == 1);

    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name.to_string(), "has_fun");
}

#[test]
fn test_sorted_by_size() {
    let small = make_decl("small", Code::ret(fvar(0)));
    let medium = make_decl(
        "medium",
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(1)),
        ),
    );
    let large = make_decl(
        "large",
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(1)),
            Code::let_bind(
                LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(2)),
                Code::let_bind(
                    LetDecl::new(fvar(3), name("_3"), nat_type(), LetValue::nat(3)),
                    Code::ret(fvar(3)),
                ),
            ),
        ),
    );

    let decls = vec![large.clone(), small.clone(), medium.clone()];
    let sorted = sorted_by_size(&decls);

    assert_eq!(sorted.len(), 3);
    assert_eq!(sorted[0].1.name.to_string(), "small");
    assert_eq!(sorted[1].1.name.to_string(), "medium");
    assert_eq!(sorted[2].1.name.to_string(), "large");
}
