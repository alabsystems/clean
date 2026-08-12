// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_parse_simple_function() {
    let mut parser = CParser::new();
    let code = r"
        int add(int a, int b) {
            return a + b;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "add");
    assert_eq!(func.params.len(), 2);
    assert_eq!(func.params[0].name, "a");
    assert_eq!(func.params[1].name, "b");
}

#[test]
fn test_parse_void_function() {
    let mut parser = CParser::new();
    let code = r"
        void noop(void) {
            return;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "noop");
    assert!(matches!(func.return_type, crate::types::CType::Void));
}

#[test]
fn test_parse_pointer_params() {
    let mut parser = CParser::new();
    let code = r"
        void swap(int *a, int *b) {
            int tmp = *a;
            *a = *b;
            *b = tmp;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "swap");
    assert_eq!(func.params.len(), 2);
    assert!(matches!(func.params[0].ty, crate::types::CType::Pointer(_)));
}

#[test]
fn test_parse_if_statement() {
    let mut parser = CParser::new();
    let code = r"
        int abs(int x) {
            if (x < 0) {
                return -x;
            }
            return x;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "abs");

    // Check body contains if statement
    match func.body.as_ref() {
        crate::stmt::CStmt::Block(stmts) => {
            assert!(stmts.len() >= 2);
            assert!(matches!(stmts[0], crate::stmt::CStmt::If { .. }));
        }
        _ => panic!("Expected block"),
    }
}

#[test]
fn test_parse_for_loop() {
    let mut parser = CParser::new();
    let code = r"
        int sum(int n) {
            int total = 0;
            for (int i = 0; i < n; i++) {
                total += i;
            }
            return total;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "sum");
}

#[test]
fn test_parse_while_loop() {
    let mut parser = CParser::new();
    let code = r"
        int count_down(int n) {
            while (n > 0) {
                n--;
            }
            return n;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "count_down");
}

#[test]
fn test_parse_struct() {
    let mut parser = CParser::new();
    let code = r"
        struct Point {
            int x;
            int y;
        };

        int get_x(struct Point p) {
            return p.x;
        }
    ";

    let funcs = parser.parse_translation_unit(code).unwrap();
    assert_eq!(funcs.len(), 1);
    assert_eq!(funcs[0].name, "get_x");
}

#[test]
fn test_parse_bitfield_struct_records_widths_and_separator() {
    // The parser must record bit-field widths, the unnamed zero-width
    // separator, and an ordinary trailing member.
    let mut parser = CParser::new();
    let code = r"
        struct Flags { unsigned a : 3; unsigned b : 5; unsigned : 0; int c; }
        flags(void) { struct Flags f; return f; }
    ";
    let func = parser
        .parse_function(code)
        .expect("bit-field struct should parse");
    let crate::types::CType::Struct { fields, .. } = func.return_type.unqualified() else {
        panic!("expected struct return type, got {:?}", func.return_type);
    };
    // a, b, the zero-width separator, and c.
    assert_eq!(fields.len(), 4);
    assert_eq!(
        (fields[0].name.as_str(), fields[0].bit_width),
        ("a", Some(3))
    );
    assert_eq!(
        (fields[1].name.as_str(), fields[1].bit_width),
        ("b", Some(5))
    );
    assert_eq!(fields[2].name, "", "zero-width separator is unnamed");
    assert_eq!(fields[2].bit_width, Some(0));
    assert_eq!(fields[3].name, "c");
    assert_eq!(fields[3].bit_width, None, "c is an ordinary member");
}

#[test]
fn test_parse_struct_flexible_array_member_is_incomplete_array() {
    // C99 6.7.2.1p18: `int arr[]` as the last struct member is a flexible
    // array member, parsed as an incomplete array type, and sizeof(S) counts
    // only the leading `int x` (the FAM contributes 0).
    let mut parser = CParser::new();
    let code = r"
        struct S { int x; int arr[]; }
        make(void) { struct S s; return s; }
    ";
    let func = parser
        .parse_function(code)
        .expect("struct with a flexible array member should parse");
    let crate::types::CType::Struct { fields, .. } = func.return_type.unqualified() else {
        panic!("expected struct return type, got {:?}", func.return_type);
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].name, "x");
    assert_eq!(fields[1].name, "arr");
    assert!(
        matches!(fields[1].ty, crate::types::CType::IncompleteArray(_)),
        "trailing `int arr[]` must be an incomplete array, got {:?}",
        fields[1].ty
    );
    assert_eq!(
        func.return_type.unqualified().size(),
        4,
        "FAM omitted from sizeof(S)"
    );
}

#[test]
fn test_parse_struct_zero_length_array_member_is_fixed_array() {
    // `int arr[0]` is a (zero-length) fixed array, NOT a flexible array
    // member — it is distinguished by the explicit `0` dimension.
    let mut parser = CParser::new();
    let code = r"
        struct S { int x; int arr[0]; }
        make(void) { struct S s; return s; }
    ";
    let func = parser
        .parse_function(code)
        .expect("struct with a zero-length array member should parse");
    let crate::types::CType::Struct { fields, .. } = func.return_type.unqualified() else {
        panic!("expected struct return type, got {:?}", func.return_type);
    };
    assert!(
        matches!(fields[1].ty, crate::types::CType::Array(_, 0)),
        "`int arr[0]` must be a fixed zero-length array, got {:?}",
        fields[1].ty
    );
}

#[test]
fn test_parse_struct_flexible_array_not_last_is_rejected() {
    // C99 6.7.2.1p18: a flexible array member must be the LAST member.
    let mut parser = CParser::new();
    let code = r"
        struct S { int arr[]; int y; }
        make(void) { struct S s; return s; }
    ";
    let err = parser
        .parse_function(code)
        .expect_err("FAM that is not the last member must be rejected");
    assert!(
        matches!(err, ParseError::TypeError { .. }),
        "expected a TypeError, got {err:?}"
    );
}

#[test]
fn test_parse_struct_flexible_array_sole_member_is_rejected() {
    // C99 6.7.2.1p18: a FAM cannot be the only member of the struct.
    let mut parser = CParser::new();
    let code = r"
        struct S { int arr[]; }
        make(void) { struct S s; return s; }
    ";
    let err = parser
        .parse_function(code)
        .expect_err("FAM as sole member must be rejected");
    assert!(
        matches!(err, ParseError::TypeError { .. }),
        "expected a TypeError, got {err:?}"
    );
}

#[test]
fn test_parse_array_param() {
    let mut parser = CParser::new();
    let code = r"
        int sum_array(int arr[], int n) {
            int sum = 0;
            for (int i = 0; i < n; i++) {
                sum += arr[i];
            }
            return sum;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "sum_array");
    assert!(matches!(func.params[0].ty, crate::types::CType::Pointer(_)));
}

#[test]
fn test_parse_cast() {
    let mut parser = CParser::new();
    let code = r"
        void* to_void(int* p) {
            return (void*)p;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "to_void");
}

#[test]
fn test_parse_ternary() {
    let mut parser = CParser::new();
    let code = r"
        int max(int a, int b) {
            return a > b ? a : b;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "max");
}

#[test]
fn test_parse_sizeof() {
    let mut parser = CParser::new();
    let code = r"
        int get_int_size(void) {
            return sizeof(int);
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "get_int_size");
}

#[test]
fn test_parse_multiple_functions() {
    let mut parser = CParser::new();
    let code = r"
        int add(int a, int b) { return a + b; }
        int sub(int a, int b) { return a - b; }
        int mul(int a, int b) { return a * b; }
    ";

    let funcs = parser.parse_translation_unit(code).unwrap();
    assert_eq!(funcs.len(), 3);
    assert_eq!(funcs[0].name, "add");
    assert_eq!(funcs[1].name, "sub");
    assert_eq!(funcs[2].name, "mul");
}

#[test]
fn test_parse_variadic_function() {
    let mut parser = CParser::new();
    let code = r"
        int printf_wrapper(const char* fmt, ...) {
            return 0;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "printf_wrapper");
    assert!(func.variadic);
}

#[test]
fn test_parse_static_function() {
    let mut parser = CParser::new();
    let code = r"
        static int helper(int x) {
            return x * 2;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "helper");
    assert_eq!(func.storage, crate::stmt::StorageClass::Static);
}

#[test]
fn test_parse_noreturn_specifier_sets_flag() {
    let mut parser = CParser::new();
    let code = r"
        _Noreturn void die(void) {
            abort();
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "die");
    assert!(
        func.is_noreturn,
        "_Noreturn specifier should set is_noreturn"
    );
}

#[test]
fn test_parse_noreturn_macro_form_sets_flag() {
    // <stdnoreturn.h> defines `noreturn` as a macro expanding to `_Noreturn`;
    // tree-sitter-c surfaces the bare keyword as a type_qualifier too.
    let mut parser = CParser::new();
    let code = r"
        noreturn void die(void) {
            abort();
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert!(func.is_noreturn, "noreturn keyword should set is_noreturn");
}

#[test]
fn test_parse_plain_function_is_not_noreturn() {
    let mut parser = CParser::new();
    let code = r"
        void f(void) {
            return;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert!(
        !func.is_noreturn,
        "a function without _Noreturn must not be marked noreturn"
    );
}

#[test]
fn test_parse_noreturn_falling_off_end_is_flagged() {
    // _Noreturn void g(void) { } -- falls off the end, which is UB (6.7.4p2).
    let mut parser = CParser::new();
    let code = r"
        _Noreturn void g(void) {
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert!(func.is_noreturn);
    assert_eq!(
        crate::noreturn::check_func(&func),
        Some(crate::ub::UBKind::NoreturnReturns("g".to_string())),
        "a parsed _Noreturn function that falls off the end must be flagged"
    );
}

#[test]
fn test_parse_noreturn_with_abort_passes_check() {
    // _Noreturn void die(void) { abort(); } -- genuinely diverges.
    let mut parser = CParser::new();
    let code = r"
        _Noreturn void die(void) {
            abort();
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(
        crate::noreturn::check_func(&func),
        None,
        "a _Noreturn function that always aborts must pass the check"
    );
}

#[test]
fn test_parse_number_literals() {
    let mut parser = CParser::new();
    let code = r"
        int literals(void) {
            int a = 42;
            int b = 0xFF;
            int c = 077;
            return a + b + c;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "literals");
}

#[test]
fn test_parse_switch() {
    let mut parser = CParser::new();
    let code = r"
        int switch_test(int x) {
            switch (x) {
                case 0: return 1;
                case 1: return 2;
                default: return 0;
            }
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "switch_test");
}

#[test]
fn test_acsl_spec_parsing() {
    let comment = r"/*@
        requires x >= 0;
        ensures \result >= 0;
        assigns \nothing;
    */";

    let spec = parse_acsl_spec(comment).unwrap();
    assert_eq!(spec.requires.len(), 1);
    assert_eq!(spec.ensures.len(), 1);
}

#[test]
fn test_parse_do_while() {
    let mut parser = CParser::new();
    let code = r"
        int do_loop(int n) {
            int i = 0;
            do {
                i++;
            } while (i < n);
            return i;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "do_loop");
}

#[test]
fn test_parse_goto_label() {
    let mut parser = CParser::new();
    let code = r"
        void with_goto(void) {
            goto end;
            return;
        end:
            return;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "with_goto");
}

#[test]
fn test_parse_pointer_return() {
    let mut parser = CParser::new();
    let code = r"
        int* get_ptr(int* p) {
            return p;
        }
    ";

    let func = parser.parse_function(code).unwrap();
    assert_eq!(func.name, "get_ptr");
    assert!(matches!(func.return_type, crate::types::CType::Pointer(_)));
}

#[test]
fn test_parse_function_with_acsl_block_spec_attached() {
    let mut parser = CParser::new();
    let code = r"
        /*@
            requires x >= 0;
            ensures \result >= 0;
        */
        int clamp(int x) { return x; }
    ";

    let vf = parser.parse_function_with_spec(code).unwrap();
    assert_eq!(vf.name, "clamp");
    assert_eq!(vf.spec.requires.len(), 1);
    assert_eq!(vf.spec.ensures.len(), 1);
    assert!(!vf.generate_vcs().is_empty());
}

#[test]
fn test_parse_translation_unit_with_line_acsl_spec() {
    let mut parser = CParser::new();
    let code = r"
        //@ requires n >= 0;
        //@ ensures \result >= 0;
        int id(int n) { return n; }

        int plain(int x) { return x; }
    ";

    let funcs = parser.parse_translation_unit_with_specs(code).unwrap();
    assert_eq!(funcs.len(), 2);
    assert_eq!(funcs[0].name, "id");
    assert_eq!(funcs[0].spec.requires.len(), 1);
    assert_eq!(funcs[0].spec.ensures.len(), 1);
    assert!(funcs[1].spec.requires.is_empty());
    assert!(funcs[1].spec.ensures.is_empty());
}

// ---------------------------------------------------------------------------
// ACSL spec-expression parser (`parse_spec_expr`) — precedence-aware,
// parenthesis-aware recursive-descent parsing of requires/ensures terms.
// ---------------------------------------------------------------------------

mod acsl_spec_expr {
    use super::parse_acsl_spec;
    use crate::expr::{BinOp, UnaryOp};
    use crate::spec::Spec;

    /// Parse a single `requires <expr>;` clause and return the resulting `Spec`.
    fn req(expr: &str) -> Spec {
        let comment = format!("//@ requires {expr};");
        let spec = parse_acsl_spec(&comment).expect("acsl spec should parse");
        assert_eq!(spec.requires.len(), 1, "expected one requires clause");
        spec.requires.into_iter().next().unwrap()
    }

    #[test]
    fn test_parse_spec_expr_simple_comparison_returns_binop() {
        // x >= 0  =>  BinOp(Ge, Var(x), Int(0))
        let spec = req("x >= 0");
        match spec {
            Spec::BinOp {
                op: BinOp::Ge,
                left,
                right,
            } => {
                assert_eq!(*left, Spec::Var("x".to_string()));
                assert_eq!(*right, Spec::Int(0));
            }
            other => panic!("expected Ge binop, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_conjunction_returns_and() {
        // a > 0 && b < 10  =>  And([Gt(a,0), Lt(b,10)])
        let spec = req("a > 0 && b < 10");
        match spec {
            Spec::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2);
                assert!(matches!(conjuncts[0], Spec::BinOp { op: BinOp::Gt, .. }));
                assert!(matches!(conjuncts[1], Spec::BinOp { op: BinOp::Lt, .. }));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_valid_with_conjunction_does_not_missplit() {
        // SOUNDNESS REGRESSION: the old naive split_once(">=") split *inside*
        // `\valid(p)` / across the `&&`, producing a malformed
        // Spec::Var("\\valid(p) && x"). The paren-aware parser must instead
        // produce And([Valid(Var p), Ge(Var x, Int 0)]).
        let spec = req("\\valid(p) && x >= 0");
        match spec {
            Spec::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2);
                match &conjuncts[0] {
                    Spec::Valid(inner) => assert_eq!(**inner, Spec::Var("p".to_string())),
                    other => panic!("expected \\valid, got {other:?}"),
                }
                assert!(matches!(conjuncts[1], Spec::BinOp { op: BinOp::Ge, .. }));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_separated_returns_separated_list() {
        // \separated(p, q, r)  =>  Separated([Var p, Var q, Var r])
        let spec = req("\\separated(p, q, r)");
        match spec {
            Spec::Separated(parts) => {
                assert_eq!(parts.len(), 3);
                assert_eq!(parts[0], Spec::Var("p".to_string()));
                assert_eq!(parts[1], Spec::Var("q".to_string()));
                assert_eq!(parts[2], Spec::Var("r".to_string()));
            }
            other => panic!("expected Separated, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_valid_read_and_null_keywords() {
        assert!(matches!(req("\\valid_read(p)"), Spec::ValidRead(_)));
        match req("p == \\null") {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                right,
            } => {
                assert_eq!(*left, Spec::Var("p".to_string()));
                assert_eq!(*right, Spec::Null);
            }
            other => panic!("expected Eq with Null, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_implication_is_right_associative() {
        // a ==> b ==> c  =>  Implies(a, Implies(b, c))
        let spec = req("a ==> b ==> c");
        match spec {
            Spec::Implies(p, q) => {
                assert_eq!(*p, Spec::Var("a".to_string()));
                match *q {
                    Spec::Implies(p2, q2) => {
                        assert_eq!(*p2, Spec::Var("b".to_string()));
                        assert_eq!(*q2, Spec::Var("c".to_string()));
                    }
                    other => panic!("expected nested Implies, got {other:?}"),
                }
            }
            other => panic!("expected Implies, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_logical_binds_looser_than_comparison() {
        // x > 0 ==> \valid(p)  parses the comparison on the LHS of the arrow.
        let spec = req("x > 0 ==> \\valid(p)");
        match spec {
            Spec::Implies(p, q) => {
                assert!(matches!(*p, Spec::BinOp { op: BinOp::Gt, .. }));
                assert!(matches!(*q, Spec::Valid(_)));
            }
            other => panic!("expected Implies, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_arithmetic_precedence() {
        // a + b * c == 0  =>  Eq(Add(a, Mul(b, c)), 0)  (mul binds tighter)
        let spec = req("a + b * c == 0");
        match spec {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                ..
            } => match *left {
                Spec::BinOp {
                    op: BinOp::Add,
                    left: add_l,
                    right: add_r,
                } => {
                    assert_eq!(*add_l, Spec::Var("a".to_string()));
                    assert!(matches!(*add_r, Spec::BinOp { op: BinOp::Mul, .. }));
                }
                other => panic!("expected Add on lhs, got {other:?}"),
            },
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_parens_override_precedence() {
        // (a + b) * c == 0  =>  Eq(Mul(Add(a, b), c), 0)
        let spec = req("(a + b) * c == 0");
        match spec {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                ..
            } => match *left {
                Spec::BinOp {
                    op: BinOp::Mul,
                    left: mul_l,
                    right: mul_r,
                } => {
                    assert!(matches!(*mul_l, Spec::BinOp { op: BinOp::Add, .. }));
                    assert_eq!(*mul_r, Spec::Var("c".to_string()));
                }
                other => panic!("expected Mul on lhs, got {other:?}"),
            },
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_unary_not_and_neg() {
        match req("!done") {
            Spec::Not(inner) => assert_eq!(*inner, Spec::Var("done".to_string())),
            other => panic!("expected Not, got {other:?}"),
        }
        // x == -1: the '-' is unary negation, not a top-level subtraction.
        match req("x == -1") {
            Spec::BinOp {
                op: BinOp::Eq,
                right,
                ..
            } => match *right {
                Spec::UnaryOp {
                    op: UnaryOp::Neg,
                    operand,
                } => assert_eq!(*operand, Spec::Int(1)),
                other => panic!("expected unary Neg, got {other:?}"),
            },
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_logic_call_with_commas_not_missplit() {
        // f(a, b) == c: the comma inside the call must not be parsed as a
        // top-level separator, and the call head is preserved.
        let spec = req("f(a, b) == c");
        match spec {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                right,
            } => {
                match *left {
                    Spec::Call { func, args } => {
                        assert_eq!(func, "f");
                        assert_eq!(args.len(), 2);
                    }
                    other => panic!("expected Call, got {other:?}"),
                }
                assert_eq!(*right, Spec::Var("c".to_string()));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_result_and_old_builtins() {
        // \result == \old(x)
        let spec = req("\\result == \\old(x)");
        match spec {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                right,
            } => {
                assert_eq!(*left, Spec::Result);
                match *right {
                    Spec::Old(inner) => assert_eq!(*inner, Spec::Var("x".to_string())),
                    other => panic!("expected Old, got {other:?}"),
                }
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_disjunction_of_equalities() {
        // \result == x || \result == -x  =>  Or([Eq(.., x), Eq(.., Neg x)])
        let spec = req("\\result == x || \\result == -x");
        match spec {
            Spec::Or(disjuncts) => {
                assert_eq!(disjuncts.len(), 2);
                assert!(matches!(disjuncts[0], Spec::BinOp { op: BinOp::Eq, .. }));
                match &disjuncts[1] {
                    Spec::BinOp {
                        op: BinOp::Eq,
                        right,
                        ..
                    } => assert!(matches!(
                        **right,
                        Spec::UnaryOp {
                            op: UnaryOp::Neg,
                            ..
                        }
                    )),
                    other => panic!("expected Eq, got {other:?}"),
                }
            }
            other => panic!("expected Or, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_bare_variable_fallback_unchanged() {
        // A token with no recognised operator still degrades to a Var, matching
        // the prior lenient behaviour.
        assert_eq!(req("alpha"), Spec::Var("alpha".to_string()));
    }

    #[test]
    fn test_parse_spec_expr_at_pre_label_returns_at() {
        // \at(x, Pre)  =>  At { expr: Var(x), label: "Pre" }
        let spec = req("\\at(x, Pre)");
        match spec {
            Spec::At { expr, label } => {
                assert_eq!(*expr, Spec::Var("x".to_string()));
                assert_eq!(label, "Pre");
            }
            other => panic!("expected At, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_at_index_expr_with_post_label() {
        // \at(a[i], Post): the first argument is a full spec expression
        // (a subscript), the second a standard label.
        let spec = req("\\at(a[i], Post)");
        match spec {
            Spec::At { expr, label } => {
                match *expr {
                    Spec::Index { base, index } => {
                        assert_eq!(*base, Spec::Var("a".to_string()));
                        assert_eq!(*index, Spec::Var("i".to_string()));
                    }
                    // The index sub-expression is parsed by the spec parser; if
                    // it does not model subscripts as Index it falls back to a
                    // Var of the whole `a[i]` text. Either way the label and the
                    // At wrapper are what this test pins.
                    other => assert_eq!(other, Spec::Var("a[i]".to_string())),
                }
                assert_eq!(label, "Post");
            }
            other => panic!("expected At, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_at_named_c_label_returns_at() {
        // \at(x, L): a user-defined C label name is a valid label.
        let spec = req("\\at(x, L)");
        match spec {
            Spec::At { expr, label } => {
                assert_eq!(*expr, Spec::Var("x".to_string()));
                assert_eq!(label, "L");
            }
            other => panic!("expected At, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_at_here_label_in_comparison() {
        // \at(x, Here) == y: the At term composes inside a comparison without
        // the comma inside \at being mis-split as a top-level separator.
        let spec = req("\\at(x, Here) == y");
        match spec {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                right,
            } => {
                match *left {
                    Spec::At { expr, label } => {
                        assert_eq!(*expr, Spec::Var("x".to_string()));
                        assert_eq!(label, "Here");
                    }
                    other => panic!("expected At on lhs, got {other:?}"),
                }
                assert_eq!(*right, Spec::Var("y".to_string()));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_at_missing_label_does_not_construct_at() {
        // \at(x): only one argument — not a valid \at. It must NOT silently
        // produce a Spec::At; it degrades to the lenient Var fallback.
        let spec = req("\\at(x)");
        assert!(
            !matches!(spec, Spec::At { .. }),
            "single-arg \\at must not construct At, got {spec:?}"
        );
        assert_eq!(spec, Spec::Var("\\at(x)".to_string()));
    }

    #[test]
    fn test_parse_spec_expr_at_extra_args_does_not_construct_at() {
        // \at(x, Pre, Post): three arguments — malformed. Must not construct At.
        let spec = req("\\at(x, Pre, Post)");
        assert!(
            !matches!(spec, Spec::At { .. }),
            "three-arg \\at must not construct At, got {spec:?}"
        );
        assert_eq!(spec, Spec::Var("\\at(x, Pre, Post)".to_string()));
    }

    #[test]
    fn test_parse_spec_expr_at_non_identifier_label_does_not_construct_at() {
        // \at(x, a + b): the second argument is not a single identifier, so it
        // is not a valid label. Must not construct At.
        let spec = req("\\at(x, a + b)");
        assert!(
            !matches!(spec, Spec::At { .. }),
            "non-identifier label must not construct At, got {spec:?}"
        );
    }

    // -----------------------------------------------------------------------
    // ACSL quantifiers (\forall / \exists) and bounded aggregations
    // (\sum / \product / \min / \max / \numof).
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_spec_expr_forall_builds_quantifier_node() {
        use crate::types::CType;
        // \forall int i; 0 <= i ==> a[i] >= 0
        let spec = req("\\forall(int i; 0 <= i ==> a[i] >= 0)");
        match spec {
            Spec::Forall { var, ty, body } => {
                assert_eq!(var, "i", "binder variable should be `i`");
                assert_eq!(ty, CType::int(), "binder type should be `int`");
                // body is an implication 0 <= i ==> a[i] >= 0
                match *body {
                    Spec::Implies(lhs, rhs) => {
                        assert!(
                            matches!(*lhs, Spec::BinOp { op: BinOp::Le, .. }),
                            "implication antecedent should be `0 <= i`, got {lhs:?}"
                        );
                        assert!(
                            matches!(*rhs, Spec::BinOp { op: BinOp::Ge, .. }),
                            "implication consequent should be `a[i] >= 0`, got {rhs:?}"
                        );
                    }
                    other => panic!("expected implication body, got {other:?}"),
                }
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_exists_builds_quantifier_node() {
        use crate::types::CType;
        // \exists int k; a[k] == 0
        let spec = req("\\exists(int k; a[k] == 0)");
        match spec {
            Spec::Exists { var, ty, body } => {
                assert_eq!(var, "k");
                assert_eq!(ty, CType::int());
                assert!(
                    matches!(*body, Spec::BinOp { op: BinOp::Eq, .. }),
                    "body should be `a[k] == 0`, got {body:?}"
                );
            }
            other => panic!("expected Exists, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_forall_pointer_binder_type() {
        use crate::types::CType;
        // \forall int* p; \valid(p)
        let spec = req("\\forall(int* p; \\valid(p))");
        match spec {
            Spec::Forall { var, ty, body } => {
                assert_eq!(var, "p");
                assert_eq!(ty, CType::ptr(CType::int()), "binder type should be `int*`");
                assert!(
                    matches!(*body, Spec::Valid(_)),
                    "body should be \\valid(p), got {body:?}"
                );
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_sum_builds_aggregation_node() {
        // \result == \sum(0, n, k; a[k])
        let spec = req("\\result == \\sum(0, n, k; a[k])");
        match spec {
            Spec::BinOp {
                op: BinOp::Eq,
                left,
                right,
            } => {
                assert_eq!(*left, Spec::Result);
                match *right {
                    Spec::Sum { lo, hi, var, body } => {
                        assert_eq!(*lo, Spec::Int(0), "lower bound should be 0");
                        assert_eq!(*hi, Spec::Var("n".to_string()), "upper bound should be n");
                        assert_eq!(var, "k", "summation index should be k");
                        // The lambda body `a[k]` is captured as the body spec.
                        // (Subscript parsing is not modelled by parse_primary, so
                        // it surfaces as a compound variable reference.)
                        assert_eq!(
                            *body,
                            Spec::Var("a[k]".to_string()),
                            "lambda body should be the `a[k]` term"
                        );
                    }
                    other => panic!("expected Sum, got {other:?}"),
                }
            }
            other => panic!("expected equality with a sum, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_spec_expr_product_min_max_numof_nodes() {
        assert!(
            matches!(
                req("\\product(1, n, k; k)"),
                Spec::Product { ref var, .. } if var == "k"
            ),
            "expected Product node"
        );
        assert!(
            matches!(req("\\min(0, n, k; a[k])"), Spec::Min { .. }),
            "expected Min node"
        );
        assert!(
            matches!(req("\\max(0, n, k; a[k])"), Spec::Max { .. }),
            "expected Max node"
        );
        assert!(
            matches!(req("\\numof(0, n, k; a[k] == 0)"), Spec::NumOf { .. }),
            "expected NumOf node"
        );
    }
}

// ---------------------------------------------------------------------------
// ACSL `terminates <pred>;` function-contract clause. The parser must populate
// `FuncSpec::terminates` from the contract comment (previously dropped).
// ---------------------------------------------------------------------------

mod acsl_terminates {
    use super::parse_acsl_spec;
    use crate::expr::BinOp;
    use crate::spec::Spec;

    #[test]
    fn test_parse_terminates_comparison_populates_terminates() {
        // terminates n >= 0; => FuncSpec::terminates = Some(BinOp(Ge, n, 0))
        let comment = "//@ terminates n >= 0;";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        match spec.terminates {
            Some(Spec::BinOp {
                op: BinOp::Ge,
                left,
                right,
            }) => {
                assert_eq!(*left, Spec::Var("n".to_string()));
                assert_eq!(*right, Spec::Int(0));
            }
            other => panic!("expected terminates n >= 0, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_terminates_true_populates_true() {
        // terminates \true; => FuncSpec::terminates = Some(Spec::True)
        let comment = "//@ terminates \\true;";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(spec.terminates, Some(Spec::True));
    }

    #[test]
    fn test_parse_terminates_block_comment_populates_true() {
        // Block-comment form (/*@ ... */) must also populate terminates.
        let comment = "/*@ terminates \\true; */";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(spec.terminates, Some(Spec::True));
    }

    #[test]
    fn test_parse_terminates_composes_with_requires_and_ensures() {
        // A full contract: requires + ensures + terminates all populate.
        let comment = r"/*@
            requires n >= 0;
            ensures \result >= 0;
            terminates n >= 0;
        */";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(spec.requires.len(), 1, "expected one requires clause");
        assert_eq!(spec.ensures.len(), 1, "expected one ensures clause");
        assert!(
            spec.terminates.is_some(),
            "terminates must be populated alongside requires/ensures"
        );
        match spec.terminates {
            Some(Spec::BinOp { op: BinOp::Ge, .. }) => {}
            other => panic!("expected terminates n >= 0, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_absent_terminates_stays_none() {
        // A contract without a terminates clause leaves terminates as None.
        let comment = r"/*@
            requires x >= 0;
            ensures \result >= 0;
        */";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(spec.terminates, None, "absent terminates must stay None");
    }
}

// ---------------------------------------------------------------------------
// ACSL `reads <locations>;` function-contract clause. The parser must populate
// `FuncSpec::reads` from the contract comment (previously dropped — only
// `assigns` was parsed). The read footprint must populate independently of the
// write footprint (`assigns`) with no cross-field corruption.
// ---------------------------------------------------------------------------

mod acsl_reads {
    use super::parse_acsl_spec;
    use crate::expr::BinOp;
    use crate::spec::{Location, Spec};

    /// The location an ACSL `*p` dereference parses to. `parse_spec_expr`
    /// reads `*p` as a multiplicative expression with an empty left operand
    /// (`Var("") * Var("p")`); both the `reads` and `assigns` arms wrap the
    /// resulting spec in `Location::Deref`. This helper pins that shared shape
    /// so the tests assert the exact (and identical-to-`assigns`) footprint.
    fn deref_star(var: &str) -> Location {
        Location::Deref(Spec::BinOp {
            op: BinOp::Mul,
            left: Box::new(Spec::Var(String::new())),
            right: Box::new(Spec::Var(var.to_string())),
        })
    }

    #[test]
    fn test_parse_reads_single_deref_populates_reads() {
        // reads *p; => FuncSpec::reads = [Deref(*p)]
        let comment = "//@ reads *p;";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(
            spec.reads,
            vec![deref_star("p")],
            "single reads location must populate reads"
        );
        assert!(spec.assigns.is_empty(), "reads must not populate assigns");
    }

    #[test]
    fn test_parse_reads_nothing_populates_nothing() {
        // reads \nothing; => FuncSpec::reads = [Nothing]
        let comment = "//@ reads \\nothing;";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(
            spec.reads,
            vec![Location::Nothing],
            "reads \\nothing must populate reads with Nothing"
        );
        assert!(spec.assigns.is_empty(), "reads must not populate assigns");
    }

    #[test]
    fn test_parse_reads_block_comment_populates_reads() {
        // Block-comment form (/*@ ... */) must also populate reads.
        let comment = "/*@ reads *p; */";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(
            spec.reads,
            vec![deref_star("p")],
            "block-comment reads must populate reads"
        );
    }

    #[test]
    fn test_parse_reads_multi_location_populates_all() {
        // reads a, b; => two read locations, order preserved.
        let comment = "//@ reads a, b;";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(
            spec.reads,
            vec![
                Location::Deref(Spec::Var("a".to_string())),
                Location::Deref(Spec::Var("b".to_string())),
            ],
            "multi-location reads must populate every location in order"
        );
    }

    #[test]
    fn test_parse_reads_and_assigns_populate_independently() {
        // A full contract: requires + reads + assigns + ensures. The read and
        // write footprints must populate independently — no cross-field
        // corruption (reads goes to reads, assigns goes to assigns).
        let comment = r"/*@
            requires x >= 0;
            reads *p;
            assigns *q;
            ensures \result >= 0;
        */";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert_eq!(spec.requires.len(), 1, "expected one requires clause");
        assert_eq!(spec.ensures.len(), 1, "expected one ensures clause");
        assert_eq!(
            spec.reads,
            vec![deref_star("p")],
            "reads must hold only the read location"
        );
        assert_eq!(
            spec.assigns,
            vec![deref_star("q")],
            "assigns must hold only the written location"
        );
    }

    #[test]
    fn test_parse_absent_reads_stays_empty() {
        // A contract without a reads clause leaves reads empty.
        let comment = r"/*@
            requires x >= 0;
            assigns *q;
            ensures \result >= 0;
        */";
        let spec = parse_acsl_spec(comment).expect("acsl spec should parse");
        assert!(
            spec.reads.is_empty(),
            "absent reads clause must leave reads empty"
        );
        assert_eq!(
            spec.assigns,
            vec![deref_star("q")],
            "assigns must still populate when reads is absent"
        );
    }
}

#[cfg(test)]
mod designated_init_tests {
    use super::*;
    use crate::expr::{CExpr, Designator, Initializer};
    use crate::stmt::CStmt;

    /// Extract the initializer of the first declaration in a function body.
    fn first_decl_init(source: &str) -> Initializer {
        let mut parser = CParser::new();
        let func = parser.parse_function(source).expect("parse should succeed");
        match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Decl(decl)) => decl
                    .init
                    .clone()
                    .expect("declaration should have an initializer"),
                other => panic!("expected first stmt to be a declaration, got {other:?}"),
            },
            other => panic!("expected function body block, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_struct_field_designators_produces_designated_inits() {
        let init = first_decl_init(
            r"
            void f(void) {
                struct P p = { .x = 1, .y = 2 };
            }
            ",
        );
        let items = match init {
            Initializer::List(items) => items,
            other => panic!("expected initializer list, got {other:?}"),
        };
        assert_eq!(items.len(), 2);
        match &items[0] {
            Initializer::Designated { designator, init } => {
                assert_eq!(*designator, Designator::Field("x".to_string()));
                assert_eq!(**init, Initializer::Expr(CExpr::IntLit(1)));
            }
            other => panic!("expected designated init, got {other:?}"),
        }
        match &items[1] {
            Initializer::Designated { designator, init } => {
                assert_eq!(*designator, Designator::Field("y".to_string()));
                assert_eq!(**init, Initializer::Expr(CExpr::IntLit(2)));
            }
            other => panic!("expected designated init, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_array_index_designators_produces_index_designators() {
        let init = first_decl_init(
            r"
            void f(void) {
                int a[5] = { [2] = 7, [4] = 9 };
            }
            ",
        );
        let items = match init {
            Initializer::List(items) => items,
            other => panic!("expected initializer list, got {other:?}"),
        };
        assert_eq!(items.len(), 2);
        match &items[0] {
            Initializer::Designated { designator, init } => {
                assert_eq!(*designator, Designator::Index(Box::new(CExpr::IntLit(2))));
                assert_eq!(**init, Initializer::Expr(CExpr::IntLit(7)));
            }
            other => panic!("expected designated init, got {other:?}"),
        }
        match &items[1] {
            Initializer::Designated { designator, .. } => {
                assert_eq!(*designator, Designator::Index(Box::new(CExpr::IntLit(4))));
            }
            other => panic!("expected designated init, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_chained_field_designator_produces_chain() {
        let init = first_decl_init(
            r"
            void f(void) {
                struct Q q = { .a.b = 3 };
            }
            ",
        );
        let items = match init {
            Initializer::List(items) => items,
            other => panic!("expected initializer list, got {other:?}"),
        };
        assert_eq!(items.len(), 1);
        match &items[0] {
            Initializer::Designated { designator, init } => {
                assert_eq!(
                    *designator,
                    Designator::Chain(vec![
                        Designator::Field("a".to_string()),
                        Designator::Field("b".to_string()),
                    ])
                );
                assert_eq!(**init, Initializer::Expr(CExpr::IntLit(3)));
            }
            other => panic!("expected designated init, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_mixed_designated_and_positional_preserves_order() {
        let init = first_decl_init(
            r"
            void f(void) {
                int m[3] = { 1, [2] = 5, 6 };
            }
            ",
        );
        let items = match init {
            Initializer::List(items) => items,
            other => panic!("expected initializer list, got {other:?}"),
        };
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], Initializer::Expr(CExpr::IntLit(1)));
        match &items[1] {
            Initializer::Designated { designator, init } => {
                assert_eq!(*designator, Designator::Index(Box::new(CExpr::IntLit(2))));
                assert_eq!(**init, Initializer::Expr(CExpr::IntLit(5)));
            }
            other => panic!("expected designated init, got {other:?}"),
        }
        assert_eq!(items[2], Initializer::Expr(CExpr::IntLit(6)));
    }
}

#[cfg(test)]
mod alignof_tests {
    use super::*;
    use crate::expr::CExpr;
    use crate::stmt::CStmt;
    use crate::types::{CType, IntKind, Signedness};

    /// Extract the expression returned by the first `return` statement in a
    /// function body parsed from `source`.
    fn first_return_expr(source: &str) -> CExpr {
        let mut parser = CParser::new();
        let func = parser.parse_function(source).expect("parse should succeed");
        match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Return(Some(expr))) => expr.clone(),
                other => panic!("expected first stmt to be `return expr;`, got {other:?}"),
            },
            other => panic!("expected function body block, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_alignof_int_produces_alignof_type_node() {
        let expr = first_return_expr("int f(void) { return _Alignof(int); }");
        match expr {
            CExpr::AlignOf(CType::Int(IntKind::Int, Signedness::Signed)) => {}
            other => panic!("expected AlignOf(int), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_alignof_char_produces_alignof_type_node() {
        let expr = first_return_expr("int f(void) { return _Alignof(char); }");
        match expr {
            CExpr::AlignOf(CType::Int(IntKind::Char, _)) => {}
            other => panic!("expected AlignOf(char), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_alignof_double_produces_alignof_type_node() {
        let expr = first_return_expr("int f(void) { return _Alignof(double); }");
        match expr {
            CExpr::AlignOf(CType::Float(crate::types::FloatKind::Double)) => {}
            other => panic!("expected AlignOf(double), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_alignof_struct_produces_alignof_struct_node() {
        let expr = first_return_expr("int f(void) { return _Alignof(struct Point); }");
        match expr {
            CExpr::AlignOf(CType::Struct { name, .. }) => {
                assert_eq!(name.as_deref(), Some("Point"));
            }
            other => panic!("expected AlignOf(struct Point), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_lowercase_alignof_macro_produces_alignof_node() {
        // `alignof` is the `<stdalign.h>` macro spelling of `_Alignof`.
        let expr = first_return_expr("int f(void) { return alignof(double); }");
        match expr {
            CExpr::AlignOf(CType::Float(crate::types::FloatKind::Double)) => {}
            other => panic!("expected AlignOf(double), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_then_eval_alignof_int_yields_four() {
        // End-to-end: the parsed `_Alignof(int)` evaluates to alignof(int) = 4.
        let expr = first_return_expr("int f(void) { return _Alignof(int); }");
        let mut state = crate::eval::State::new();
        let val = state
            .eval_expr_to_value(&expr)
            .expect("alignof should evaluate");
        assert_eq!(val, crate::values::CValue::UInt(4));
    }

    #[test]
    fn test_parse_then_eval_alignof_double_yields_eight() {
        let expr = first_return_expr("int f(void) { return _Alignof(double); }");
        let mut state = crate::eval::State::new();
        let val = state
            .eval_expr_to_value(&expr)
            .expect("alignof should evaluate");
        assert_eq!(val, crate::values::CValue::UInt(8));
    }
}

#[cfg(test)]
mod static_assert_tests {
    use super::*;
    use crate::eval::{check_static_assert, State, StaticAssertError};
    use crate::expr::CExpr;
    use crate::stmt::CStmt;

    /// Parse `source` (a function body containing the assertion) and return the
    /// first statement of the body.
    fn first_body_stmt(source: &str) -> CStmt {
        let mut parser = CParser::new();
        let func = parser.parse_function(source).expect("parse should succeed");
        match func.body.as_ref() {
            CStmt::Block(stmts) => stmts
                .first()
                .cloned()
                .expect("function body should have at least one statement"),
            other => panic!("expected function body block, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_static_assert_two_args_produces_static_assert_with_message() {
        let stmt = first_body_stmt(r#"void f(void) { _Static_assert(1, "ok"); }"#);
        match stmt {
            CStmt::StaticAssert { cond, message } => {
                assert_eq!(cond, CExpr::IntLit(1));
                assert_eq!(message.as_deref(), Some("ok"));
            }
            other => panic!("expected StaticAssert, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_static_assert_lowercase_spelling_produces_static_assert() {
        // `static_assert` is the `<assert.h>` macro spelling of `_Static_assert`.
        let stmt = first_body_stmt(r#"void f(void) { static_assert(1, "ok"); }"#);
        assert!(
            matches!(stmt, CStmt::StaticAssert { .. }),
            "lowercase static_assert should parse to StaticAssert, got {stmt:?}"
        );
    }

    #[test]
    fn test_parse_static_assert_single_arg_c23_form_has_no_message() {
        // C23 allows omitting the message.
        let stmt = first_body_stmt("void f(void) { _Static_assert(1); }");
        match stmt {
            CStmt::StaticAssert { cond, message } => {
                assert_eq!(cond, CExpr::IntLit(1));
                assert_eq!(message, None);
            }
            other => panic!("expected StaticAssert without message, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_static_assert_preserves_relational_condition() {
        let stmt = first_body_stmt(r#"void f(void) { _Static_assert(sizeof(int) >= 2, "size"); }"#);
        match stmt {
            CStmt::StaticAssert { message, .. } => {
                assert_eq!(message.as_deref(), Some("size"));
            }
            other => panic!("expected StaticAssert, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_ordinary_call_is_not_static_assert() {
        // A normal function call must remain an expression statement.
        let stmt = first_body_stmt("void f(void) { g(1, 2); }");
        assert!(
            matches!(stmt, CStmt::Expr(CExpr::Call { .. })),
            "ordinary call should stay an Expr(Call), got {stmt:?}"
        );
    }

    #[test]
    fn test_check_static_assert_true_literal_passes() {
        check_static_assert(&CExpr::int(1), Some("ok")).expect("1 should pass");
    }

    #[test]
    fn test_check_static_assert_sizeof_int_ge_two_passes() {
        // sizeof(int) >= 2 holds in this model (sizeof(int) == 4).
        let cond = CExpr::binop(
            crate::expr::BinOp::Ge,
            CExpr::SizeOf(crate::expr::SizeOfArg::Type(crate::types::CType::int())),
            CExpr::int(2),
        );
        check_static_assert(&cond, Some("size")).expect("sizeof(int) >= 2 should pass");
    }

    #[test]
    fn test_check_static_assert_zero_literal_fails_with_message() {
        let err = check_static_assert(&CExpr::int(0), Some("fail"))
            .expect_err("0 should fail the assertion");
        match err {
            StaticAssertError::AssertionFailed { message } => assert_eq!(message, "fail"),
            other => panic!("expected AssertionFailed, got {other:?}"),
        }
    }

    #[test]
    fn test_check_static_assert_false_relation_fails_with_message() {
        // 1 == 2 is false.
        let cond = CExpr::binop(crate::expr::BinOp::Eq, CExpr::int(1), CExpr::int(2));
        let err =
            check_static_assert(&cond, Some("neq")).expect_err("1 == 2 should fail the assertion");
        assert_eq!(
            err,
            StaticAssertError::AssertionFailed {
                message: "neq".to_string()
            }
        );
    }

    #[test]
    fn test_check_static_assert_missing_message_uses_default_text() {
        let err =
            check_static_assert(&CExpr::int(0), None).expect_err("0 should fail the assertion");
        match err {
            StaticAssertError::AssertionFailed { message } => {
                assert_eq!(message, "static assertion failed");
            }
            other => panic!("expected AssertionFailed, got {other:?}"),
        }
    }

    #[test]
    fn test_check_static_assert_non_constant_expression_is_rejected() {
        // A bare variable reference is not an integer constant expression.
        let err = check_static_assert(&CExpr::var("x"), Some("nope"))
            .expect_err("a non-constant expression should be rejected");
        assert!(
            matches!(err, StaticAssertError::NotConstant { .. }),
            "expected NotConstant, got {err:?}"
        );
    }

    #[test]
    fn test_parse_then_check_false_static_assert_is_rejected() {
        // End-to-end: parse a false assertion and confirm the checker rejects it.
        let stmt = first_body_stmt(r#"void f(void) { _Static_assert(0, "boom"); }"#);
        match stmt {
            CStmt::StaticAssert { cond, message } => {
                let err = check_static_assert(&cond, message.as_deref())
                    .expect_err("0 assertion must be rejected");
                assert_eq!(
                    err,
                    StaticAssertError::AssertionFailed {
                        message: "boom".to_string()
                    }
                );
            }
            other => panic!("expected StaticAssert, got {other:?}"),
        }
    }

    #[test]
    fn test_exec_stmt_false_static_assert_errors() {
        // Executing a false static assertion must surface an error, never a
        // silent no-op, so a false assertion is never accepted.
        let stmt = CStmt::static_assert(CExpr::int(0), Some("runtime fail".to_string()));
        let mut state = State::new();
        let result = crate::eval::Interpreter::new(&mut state).exec_stmt(&stmt);
        assert!(
            result.is_err(),
            "executing a false static assertion should error, got {result:?}"
        );
    }

    #[test]
    fn test_parse_then_check_sizeof_static_assert_passes() {
        // End-to-end: `_Static_assert(sizeof(int) >= 2, "..")` parses and the
        // controlling constant expression evaluates true (sizeof(int) == 4).
        let stmt = first_body_stmt(r#"void f(void) { _Static_assert(sizeof(int) >= 2, "ge"); }"#);
        match stmt {
            CStmt::StaticAssert { cond, message } => {
                check_static_assert(&cond, message.as_deref())
                    .expect("sizeof(int) >= 2 should hold");
            }
            other => panic!("expected StaticAssert, got {other:?}"),
        }
    }

    #[test]
    fn test_exec_stmt_true_static_assert_is_noop() {
        let stmt = CStmt::static_assert(CExpr::int(1), Some("ok".to_string()));
        let mut state = State::new();
        let flow = crate::eval::Interpreter::new(&mut state)
            .exec_stmt(&stmt)
            .expect("a true static assertion should execute as a no-op");
        assert_eq!(flow, crate::eval::ControlFlow::Continue);
    }
}

#[test]
fn test_parse_restrict_pointer_param_sets_is_restrict() {
    use crate::types::CType;

    let mut parser = CParser::new();
    let func = parser
        .parse_function("void f(int * restrict p) { return; }")
        .expect("should parse restrict-qualified pointer parameter");

    assert_eq!(func.params.len(), 1);
    assert_eq!(func.params[0].name, "p");
    match &func.params[0].ty {
        CType::Qualified {
            ty,
            is_const,
            is_volatile,
            is_restrict,
        } => {
            assert!(*is_restrict, "restrict qualifier must be recorded");
            assert!(!*is_const, "no const was written");
            assert!(!*is_volatile, "no volatile was written");
            assert!(
                matches!(ty.as_ref(), CType::Pointer(_)),
                "restrict applies to the pointer type, got {ty:?}"
            );
        }
        other => panic!("expected Qualified pointer, got {other:?}"),
    }
}

#[test]
fn test_parse_gnu_restrict_spelling_sets_is_restrict() {
    use crate::types::CType;

    // The GNU `__restrict__` spelling is surfaced by tree-sitter-c as a
    // `type_qualifier` just like the C99 `restrict` keyword.
    let mut parser = CParser::new();
    let func = parser
        .parse_function("void g(char * __restrict__ s) { return; }")
        .expect("should parse __restrict__-qualified pointer parameter");

    match &func.params[0].ty {
        CType::Qualified {
            is_restrict, ty, ..
        } => {
            assert!(*is_restrict, "__restrict__ must set is_restrict");
            assert!(matches!(ty.as_ref(), CType::Pointer(_)));
        }
        other => panic!("expected Qualified pointer, got {other:?}"),
    }
}

#[test]
fn test_parse_plain_pointer_param_has_no_restrict() {
    use crate::types::CType;

    let mut parser = CParser::new();
    let func = parser
        .parse_function("void f(int *p) { return; }")
        .expect("should parse plain pointer parameter");

    // A non-restrict pointer is never wrapped in a Qualified layer.
    assert!(
        matches!(func.params[0].ty, CType::Pointer(_)),
        "plain pointer must stay an unqualified Pointer, got {:?}",
        func.params[0].ty
    );
}

#[test]
fn test_parse_const_pointee_param_still_parses() {
    use crate::types::CType;

    // `const int *q`: the const qualifies the pointee, NOT the pointer, so the
    // top-level type is a plain Pointer and is_restrict stays false.
    let mut parser = CParser::new();
    let func = parser
        .parse_function("void f(const int *q) { return; }")
        .expect("should parse const-pointee pointer parameter");

    assert!(
        matches!(func.params[0].ty, CType::Pointer(_)),
        "const-pointee pointer is an unqualified Pointer at top level, got {:?}",
        func.params[0].ty
    );
}

#[test]
fn test_parse_restrict_pointer_struct_field_sets_is_restrict() {
    use crate::types::CType;

    // Inline the struct definition in the parameter so the field declarations
    // are actually parsed (a forward `struct S s` reference carries no fields).
    let mut parser = CParser::new();
    let func = parser
        .parse_function("void use(struct S { int * restrict p; int *q; } s) { return; }")
        .expect("should parse a struct param with a restrict field");

    let st = func.params[0].ty.clone();
    let CType::Struct { fields, .. } = st else {
        panic!("expected struct parameter, got {st:?}");
    };

    let p = fields
        .iter()
        .find(|f| f.name == "p")
        .expect("field p should exist");
    match &p.ty {
        CType::Qualified {
            is_restrict, ty, ..
        } => {
            assert!(*is_restrict, "struct field restrict must be recorded");
            assert!(matches!(ty.as_ref(), CType::Pointer(_)));
        }
        other => panic!("expected Qualified pointer field, got {other:?}"),
    }

    let q = fields
        .iter()
        .find(|f| f.name == "q")
        .expect("field q should exist");
    assert!(
        matches!(q.ty, CType::Pointer(_)),
        "plain pointer field must not be restrict-qualified, got {:?}",
        q.ty
    );
}

// ---------------------------------------------------------------------------
// Regression: non-ASCII bytes in attacker-controlled ACSL comment text must
// not panic the spec-expression parser. `find_top_level`/`find_top_level_last`
// previously sliced `&s[i..]` at an arbitrary byte index `i`; for a multibyte
// UTF-8 char (e.g. 'é' = 0xC3 0xA9) `i` could land on a continuation byte,
// which is not a char boundary, triggering a hard panic (a DoS under the
// release `panic="abort"` profile). The fix guards the slice with
// `s.is_char_boundary(i)`; since all matched operators are ASCII, correct-path
// behaviour is unchanged.
#[cfg(test)]
mod acsl_spec_nonascii_no_panic {
    use super::parse_acsl_spec;
    use crate::expr::BinOp;
    use crate::spec::Spec;

    #[test]
    fn test_nonascii_in_acsl_comment_does_not_panic() {
        // 'é' = 0xC3 0xA9. Each of these previously panicked with
        // "byte index 1 is not a char boundary". Now they parse (as opaque
        // variable/expression text) without aborting the process.
        let _ = parse_acsl_spec("/*@ requires é; */");
        let _ = parse_acsl_spec("//@ requires x ==> é");
        let _ = parse_acsl_spec("//@ requires é && y");
        // Exercise find_top_level_last (arithmetic reduction) too.
        let _ = parse_acsl_spec("//@ requires é + 1 == 0");
        let _ = parse_acsl_spec("//@ requires é * 2 > 0");
        // Multibyte with a top-level operator present after it.
        let _ = parse_acsl_spec("//@ requires x == é");
    }

    #[test]
    fn test_ascii_operator_after_nonascii_still_splits() {
        // The fix must not swallow real, ASCII operators that appear after a
        // multibyte char: `é == 0` must still parse as an equality binop.
        let spec = parse_acsl_spec("//@ requires é == 0")
            .expect("acsl spec should parse")
            .requires
            .into_iter()
            .next()
            .expect("one requires clause");
        assert!(
            matches!(spec, Spec::BinOp { op: BinOp::Eq, .. }),
            "operator after a multibyte char must still split, got {spec:?}"
        );
    }
}
