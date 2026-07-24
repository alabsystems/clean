// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_simple_function() {
    // def id (x : Nat) : Nat := return x
    let decl = Decl::new(
        name("id"),
        vec![],
        Expr::const_str("Nat"),
        vec![Param::new(fvar(0), name("x"), Expr::const_str("Nat"))],
        Code::ret(fvar(0)),
        false,
    );

    let s = decl.to_string();
    assert!(s.contains("def id"));
    assert!(s.contains("return"));
}

#[test]
fn test_let_binding() {
    // def const42 () : Nat :=
    //   let _1 := 42
    //   return _1
    let decl = Decl::new(
        name("const42"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let s = decl.to_string();
    assert!(s.contains("let _x1 := 42"));
    assert!(s.contains("return _x1"));
}

#[test]
fn test_case_expression() {
    // Simple case on Bool
    let cases = Cases::new(
        name("Bool"),
        Expr::const_str("Nat"),
        fvar(0),
        vec![
            Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(1))),
            Alt::ctor(name("Bool.false"), vec![], Code::ret(fvar(2))),
        ],
    );

    let code = Code::Cases(cases);
    let s = code.to_string();
    assert!(s.contains("cases _x0 of"));
    assert!(s.contains("Bool.true"));
    assert!(s.contains("Bool.false"));
}

#[test]
fn test_join_point() {
    // Join point example
    let jp_decl = FunDecl::new(
        fvar(10),
        name("jp"),
        vec![Param::new(fvar(11), name("r"), Expr::const_str("Nat"))],
        Expr::const_str("Nat"),
        Code::ret(fvar(11)),
    );

    let code = Code::join_point(jp_decl, Code::jmp(fvar(10), vec![Arg::FVar(fvar(0))]));

    let s = code.to_string();
    assert!(s.contains("jp _x10"));
    assert!(s.contains("jmp _x10"));
}

#[test]
fn test_arg_display() {
    assert_eq!(Arg::Erased.to_string(), "◇");
    assert_eq!(Arg::FVar(fvar(5)).to_string(), "_x5");
}

#[test]
fn test_extern_decl() {
    let decl = Decl::extern_decl(
        name("io_print"),
        vec![],
        Expr::const_str("IO.Unit"),
        vec![Param::new(fvar(0), name("s"), Expr::const_str("String"))],
        vec![ExternEntry {
            backend: "c".into(),
            name: "lean_io_print".into(),
        }],
    );

    assert!(decl.is_extern());
    let s = decl.to_string();
    assert!(s.contains("extern"));
    assert!(s.contains("c:lean_io_print"));
}

// ========================================================================
// Pretty-printing coverage tests (Part of #972)
// ========================================================================

#[test]
fn test_arg_display_type() {
    // Type arguments display with @ prefix
    let arg = Arg::Type(Expr::const_str("Nat"));
    let s = arg.to_string();
    assert!(s.starts_with('@'), "Type arg should start with @, got: {s}");
}

#[test]
fn test_arg_display_index() {
    assert_eq!(Arg::Index(3).to_string(), "#3");
    assert_eq!(Arg::Index(0).to_string(), "#0");
}

#[test]
fn test_let_value_display_nat_lit() {
    let v = LetValue::nat(99);
    assert_eq!(v.to_string(), "99");
}

#[test]
fn test_let_value_display_string_lit() {
    let v = LetValue::Lit(Literal::String("hello".into()));
    assert_eq!(v.to_string(), "\"hello\"");
}

#[test]
fn test_let_value_display_erased() {
    assert_eq!(LetValue::Erased.to_string(), "◇");
}

#[test]
fn test_let_value_display_proj() {
    let v = LetValue::Proj {
        type_name: name("Prod"),
        idx: 1,
        structure: fvar(7),
    };
    assert_eq!(v.to_string(), "Prod.1 _x7");
}

#[test]
fn test_let_value_display_const_no_args() {
    let v = LetValue::Const {
        name: name("Nat.zero"),
        levels: vec![],
        args: vec![],
    };
    assert_eq!(v.to_string(), "Nat.zero");
}

#[test]
fn test_let_value_display_const_with_args() {
    let v = LetValue::Const {
        name: name("Nat.add"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
    };
    assert_eq!(v.to_string(), "Nat.add _x1 _x2");
}

#[test]
fn test_let_value_display_fvar_call() {
    let v = LetValue::FVar {
        fvar: fvar(3),
        args: vec![Arg::FVar(fvar(4)), Arg::Erased],
    };
    assert_eq!(v.to_string(), "_x3 _x4 ◇");
}

#[test]
fn test_let_value_display_ctor() {
    let v = LetValue::Ctor {
        name: name("List.cons"),
        levels: vec![],
        args: vec![Arg::Type(Expr::const_str("Nat")), Arg::FVar(fvar(1))],
    };
    let s = v.to_string();
    assert!(s.starts_with("List.cons"), "got: {s}");
    assert!(s.contains("_x1"), "got: {s}");
}

#[test]
fn test_let_value_display_reuse() {
    let v = LetValue::Reuse {
        slot: fvar(5),
        ctor_name: name("List.cons"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(6))],
    };
    let s = v.to_string();
    assert!(s.contains("_reuse"), "got: {s}");
    assert!(s.contains("_x5"), "got: {s}");
    assert!(s.contains("List.cons"), "got: {s}");
    assert!(s.contains("_x6"), "got: {s}");
}

#[test]
fn test_code_display_unreachable() {
    let code = Code::Unreachable(Expr::const_str("Nat"));
    let s = code.to_string();
    assert!(s.contains("unreachable"), "got: {s}");
}

#[test]
fn test_code_display_nested_let() {
    // let _x0 := 1
    // let _x1 := 2
    // return _x1
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("a"), Expr::const_str("Nat"), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(1), name("b"), Expr::const_str("Nat"), LetValue::nat(2)),
            Code::ret(fvar(1)),
        ),
    );
    let s = code.to_string();
    assert!(s.contains("let _x0 := 1"), "got: {s}");
    assert!(s.contains("let _x1 := 2"), "got: {s}");
    assert!(s.contains("return _x1"), "got: {s}");
}

#[test]
fn test_code_display_fun() {
    // fun _x0 (_x1 _x2) :=
    //   return _x1
    // return _x0
    let fun_decl = FunDecl::new(
        fvar(0),
        name("f"),
        vec![
            Param::new(fvar(1), name("a"), Expr::const_str("Nat")),
            Param::new(fvar(2), name("b"), Expr::const_str("Nat")),
        ],
        Expr::const_str("Nat"),
        Code::ret(fvar(1)),
    );
    let code = Code::fun(fun_decl, Code::ret(fvar(0)));
    let s = code.to_string();
    assert!(s.contains("fun _x0"), "got: {s}");
    assert!(s.contains("_x1 _x2"), "got: {s}");
    assert!(s.contains("return _x0"), "got: {s}");
}

#[test]
fn test_code_display_cases_with_default() {
    let code = Code::cases(
        name("Nat"),
        Expr::const_str("Bool"),
        fvar(0),
        vec![
            Alt::ctor(name("Nat.zero"), vec![], Code::ret(fvar(1))),
            Alt::default(Code::ret(fvar(2))),
        ],
    );
    let s = code.to_string();
    assert!(s.contains("cases _x0 of"), "got: {s}");
    assert!(s.contains("| Nat.zero"), "got: {s}");
    assert!(s.contains("| _ =>"), "got: {s}");
}

#[test]
fn test_code_display_cases_with_params() {
    let code = Code::cases(
        name("List"),
        Expr::const_str("Nat"),
        fvar(0),
        vec![Alt::ctor(
            name("List.cons"),
            vec![
                Param::new(fvar(1), name("head"), Expr::const_str("Nat")),
                Param::new(fvar(2), name("tail"), Expr::const_str("List")),
            ],
            Code::ret(fvar(1)),
        )],
    );
    let s = code.to_string();
    assert!(s.contains("| List.cons _x1 _x2 =>"), "got: {s}");
}

#[test]
fn test_code_display_jmp_with_args() {
    let code = Code::jmp(
        fvar(5),
        vec![Arg::FVar(fvar(1)), Arg::Erased, Arg::FVar(fvar(3))],
    );
    let s = code.to_string();
    assert!(s.contains("jmp _x5 _x1 ◇ _x3"), "got: {s}");
}

#[test]
fn test_decl_display_recursive() {
    // Recursive declarations should still format correctly
    let decl = Decl::new(
        name("Nat.add"),
        vec![],
        Expr::const_str("Nat"),
        vec![
            Param::new(fvar(0), name("a"), Expr::const_str("Nat")),
            Param::new(fvar(1), name("b"), Expr::const_str("Nat")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("r"),
                Expr::const_str("Nat"),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        true,
    );
    let s = decl.to_string();
    assert!(s.contains("def Nat.add"), "got: {s}");
    assert!(s.contains("Nat.add _x0 _x1"), "got: {s}");
}

#[test]
fn test_decl_display_no_params() {
    // def unit () := return _x0
    let decl = Decl::new(
        name("unit"),
        vec![],
        Expr::const_str("Unit"),
        vec![],
        Code::ret(fvar(0)),
        false,
    );
    let s = decl.to_string();
    assert!(s.contains("def unit ()"), "got: {s}");
}

#[test]
fn test_extern_decl_multiple_entries() {
    let decl = Decl::extern_decl(
        name("io_read"),
        vec![],
        Expr::const_str("IO.String"),
        vec![],
        vec![
            ExternEntry {
                backend: "c".into(),
                name: "lean_io_read".into(),
            },
            ExternEntry {
                backend: "llvm".into(),
                name: "lean_io_read_llvm".into(),
            },
        ],
    );
    let s = decl.to_string();
    assert!(s.contains("[c:lean_io_read]"), "got: {s}");
    assert!(s.contains("[llvm:lean_io_read_llvm]"), "got: {s}");
}
