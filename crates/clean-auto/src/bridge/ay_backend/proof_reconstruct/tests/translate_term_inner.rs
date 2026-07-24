// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- translate_term_inner coverage tests (P1-796) ---

#[test]
fn test_translate_or() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Bool);
    let b = terms.mk_var("fvar_2", Sort::Bool);
    let or = terms.mk_or(vec![a, b]);

    let mut map = VariableMapping::new();
    map.register_var(
        "fvar_1",
        Expr::fvar(FVarId::new(1)),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    map.register_var(
        "fvar_2",
        Expr::fvar(FVarId::new(2)),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(or).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Or"),
        _ => panic!("expected Or, got {:?}", head),
    }
}

#[test]
fn test_translate_xor() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Bool);
    let b = terms.mk_var("fvar_2", Sort::Bool);
    let xor = terms.mk_xor(a, b);

    let mut map = VariableMapping::new();
    map.register_var(
        "fvar_1",
        Expr::fvar(FVarId::new(1)),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    map.register_var(
        "fvar_2",
        Expr::fvar(FVarId::new(2)),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(xor).unwrap();
    // XOR is encoded as (a ∧ ¬b) ∨ (¬a ∧ b), so top-level should be Or
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Or"),
        _ => panic!("expected Or (from XOR encoding), got {:?}", head),
    }
}

#[test]
fn test_translate_lt() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Int);
    let b = terms.mk_var("fvar_2", Sort::Int);
    let lt = terms.mk_lt(a, b);

    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty.clone());
    map.register_var("fvar_2", Expr::fvar(FVarId::new(2)), int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(lt).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "LT.lt"),
        _ => panic!("expected LT.lt, got {:?}", head),
    }
}

#[test]
fn test_translate_le() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Int);
    let b = terms.mk_var("fvar_2", Sort::Int);
    let le = terms.mk_le(a, b);

    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty.clone());
    map.register_var("fvar_2", Expr::fvar(FVarId::new(2)), int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(le).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "LE.le"),
        _ => panic!("expected LE.le, got {:?}", head),
    }
}

#[test]
fn test_translate_add() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Int);
    let b = terms.mk_var("fvar_2", Sort::Int);
    let add = terms.mk_add(vec![a, b]);

    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty.clone());
    map.register_var("fvar_2", Expr::fvar(FVarId::new(2)), int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(add).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "HAdd.hAdd"),
        _ => panic!("expected HAdd.hAdd, got {:?}", head),
    }
}

#[test]
fn test_translate_mul() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Int);
    let b = terms.mk_var("fvar_2", Sort::Int);
    let mul = terms.mk_mul(vec![a, b]);

    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty.clone());
    map.register_var("fvar_2", Expr::fvar(FVarId::new(2)), int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(mul).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "HMul.hMul"),
        _ => panic!("expected HMul.hMul, got {:?}", head),
    }
}

#[test]
fn test_translate_neg() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Int);
    let neg = terms.mk_neg(a);

    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(neg).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Neg.neg"),
        _ => panic!("expected Neg.neg, got {:?}", head),
    }
}

#[test]
fn test_translate_negative_int_constant() {
    let mut terms = TermStore::new();
    let neg_three = terms.mk_int(num_bigint::BigInt::from(-3));

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(neg_three).unwrap();
    // Should produce Int.negSucc(2) since -3 = negSucc(2) in Lean
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int.negSucc"),
        _ => panic!("expected Int.negSucc, got {:?}", head),
    }
}

#[test]
fn test_translate_positive_int_constant() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(num_bigint::BigInt::from(5));

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(five).unwrap();
    // Should produce Int.ofNat(nat_lit(5)) — Int sort wraps in Int.ofNat
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int.ofNat"),
        _ => panic!("expected Int.ofNat(...), got {:?}", result),
    }
    // The argument should be nat_lit(5)
    match result.kind() {
        ExprKind::App(_, arg) => match arg.kind() {
            ExprKind::Lit(clean_kernel::Literal::Nat(n)) => {
                assert_eq!(*n, clean_kernel::expr::BigNat::Small(5));
            }
            _ => panic!("expected arg NatLit(5), got {:?}", arg),
        },
        _ => panic!("expected App, got {:?}", result),
    }
}

#[test]
fn test_translate_uninterpreted_function() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fvar_1", Sort::Int);
    // Create an uninterpreted function application: g(x)
    let g_of_x = terms.mk_app(
        ay_core::Symbol::Named("g_func".to_string()),
        vec![x],
        Sort::Int,
    );

    let mut map = VariableMapping::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty.clone());
    // Register the function symbol
    map.register_var("g_func", Expr::fvar(FVarId::new(99)), int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(g_of_x).unwrap();
    // Should be App(fvar_99, fvar_1)
    match result.kind() {
        ExprKind::App(func, arg) => {
            match func.kind() {
                ExprKind::FVar(id) => assert_eq!(id.as_u64(), 99),
                _ => panic!("expected FVar(99) as function, got {:?}", func),
            }
            match arg.kind() {
                ExprKind::FVar(id) => assert_eq!(id.as_u64(), 1),
                _ => panic!("expected FVar(1) as arg, got {:?}", arg),
            }
        }
        _ => panic!("expected App, got {:?}", result),
    }
}

#[test]
fn test_translate_fvar_fallback_parsing() {
    // Test the fvar_N parsing fallback for unregistered variables
    let mut terms = TermStore::new();
    let x = terms.mk_var("fvar_42", Sort::Bool);

    // Do NOT register fvar_42 in the mapping — test fallback parsing
    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(x).unwrap();
    match result.kind() {
        ExprKind::FVar(id) => assert_eq!(id.as_u64(), 42),
        _ => panic!("expected FVar(42) from fallback parsing, got {:?}", result),
    }
}

#[test]
fn test_translate_unknown_variable_errors() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("unknown_var", Sort::Bool);

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(x);
    assert!(result.is_err(), "unknown variable should produce an error");
}

#[test]
fn test_translate_nary_or() {
    // Test n-ary Or: or(a, b, c) → Or(a, Or(b, c))
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Bool);
    let b = terms.mk_var("fvar_2", Sort::Bool);
    let c = terms.mk_var("fvar_3", Sort::Bool);
    let or3 = terms.mk_or(vec![a, b, c]);

    let mut map = VariableMapping::new();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), bool_ty.clone());
    map.register_var("fvar_2", Expr::fvar(FVarId::new(2)), bool_ty.clone());
    map.register_var("fvar_3", Expr::fvar(FVarId::new(3)), bool_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(or3).unwrap();
    // Top-level is Or
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Or"),
        _ => panic!("expected Or, got {:?}", head),
    }
    // Should have binary Or structure (right-associated)
    let args = result.get_app_args();
    assert_eq!(args.len(), 2, "binary Or should have 2 args");
    // Second arg should also be Or(b, c)
    let inner_head = args[1].get_app_fn();
    match inner_head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Or"),
        _ => panic!("expected nested Or, got {:?}", inner_head),
    }
}
