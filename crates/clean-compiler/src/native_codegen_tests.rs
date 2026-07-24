// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for native code generation types and lowering.
//!
//! Part of #3084 - Native code generation infrastructure.

use super::*;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::{Environment, Level, Name};

// ---------------------------------------------------------------------------
// NativeType tests
// ---------------------------------------------------------------------------

#[test]
fn test_native_type_scalar_variants() {
    assert!(NativeType::Uint8.is_scalar());
    assert!(NativeType::Uint16.is_scalar());
    assert!(NativeType::Uint32.is_scalar());
    assert!(NativeType::Uint64.is_scalar());
    assert!(NativeType::USize.is_scalar());
    assert!(NativeType::Float.is_scalar());
    assert!(NativeType::Double.is_scalar());
}

#[test]
fn test_native_type_non_scalar_variants() {
    assert!(!NativeType::Object.is_scalar());
    assert!(!NativeType::IrrelevantType.is_scalar());
    assert!(!NativeType::Closure.is_scalar());
    assert!(!NativeType::Array(Box::new(NativeType::Uint8)).is_scalar());
    assert!(!NativeType::Struct(vec![]).is_scalar());
}

#[test]
fn test_native_type_rc_variants() {
    assert!(NativeType::Object.is_rc());
    assert!(NativeType::Closure.is_rc());
    assert!(NativeType::Array(Box::new(NativeType::Uint32)).is_rc());
    assert!(NativeType::Struct(vec![("x".to_owned(), NativeType::Uint64)]).is_rc());
    // Scalars are NOT rc
    assert!(!NativeType::Uint8.is_rc());
    assert!(!NativeType::Double.is_rc());
}

#[test]
fn test_native_type_irrelevant() {
    assert!(NativeType::IrrelevantType.is_irrelevant());
    assert!(!NativeType::Object.is_irrelevant());
    assert!(!NativeType::Uint32.is_irrelevant());
}

// ---------------------------------------------------------------------------
// NativeOp tests (arithmetic)
// ---------------------------------------------------------------------------

#[test]
fn test_native_op_arithmetic_variants() {
    // Verify all arithmetic ops are distinct
    let ops = [
        NativeOp::Add,
        NativeOp::Sub,
        NativeOp::Mul,
        NativeOp::Div,
        NativeOp::Mod,
    ];
    for (i, a) in ops.iter().enumerate() {
        for (j, b) in ops.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// NativeOp tests (comparison)
// ---------------------------------------------------------------------------

#[test]
fn test_native_op_comparison_variants() {
    let ops = [
        NativeOp::Eq,
        NativeOp::Ne,
        NativeOp::Lt,
        NativeOp::Le,
        NativeOp::Gt,
        NativeOp::Ge,
    ];
    for (i, a) in ops.iter().enumerate() {
        for (j, b) in ops.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// NativeInstr tests
// ---------------------------------------------------------------------------

#[test]
fn test_native_instr_construction_with_target() {
    let instr = NativeInstr::new(
        Some("result".to_owned()),
        NativeOp::Add,
        vec![
            NativeArg::Var("a".to_owned()),
            NativeArg::Var("b".to_owned()),
        ],
    );
    assert_eq!(instr.target, Some("result".to_owned()));
    assert_eq!(instr.op, NativeOp::Add);
    assert_eq!(instr.args.len(), 2);
}

#[test]
fn test_native_instr_construction_without_target() {
    let instr = NativeInstr::new(
        None,
        NativeOp::Dealloc,
        vec![NativeArg::Var("obj".to_owned())],
    );
    assert!(instr.target.is_none());
    assert_eq!(instr.op, NativeOp::Dealloc);
    assert_eq!(instr.args.len(), 1);
}

#[test]
fn test_native_instr_call_op() {
    let instr = NativeInstr::new(
        Some("ret".to_owned()),
        NativeOp::Call("my_func".to_owned()),
        vec![NativeArg::LitInt(42)],
    );
    assert_eq!(instr.op, NativeOp::Call("my_func".to_owned()));
}

#[test]
fn test_native_instr_proj_op() {
    let instr = NativeInstr::new(
        Some("field".to_owned()),
        NativeOp::Proj(2),
        vec![NativeArg::Var("struct_val".to_owned())],
    );
    assert_eq!(instr.op, NativeOp::Proj(2));
}

#[test]
fn test_native_instr_ctor_op() {
    let instr = NativeInstr::new(
        Some("val".to_owned()),
        NativeOp::Ctor("Option.some".to_owned(), 1),
        vec![NativeArg::Var("inner".to_owned())],
    );
    assert_eq!(instr.op, NativeOp::Ctor("Option.some".to_owned(), 1));
}

// ---------------------------------------------------------------------------
// lower_expr tests (literals)
// ---------------------------------------------------------------------------

fn empty_env() -> Environment {
    Environment::new()
}

#[test]
fn test_lower_nat_literal() {
    let env = empty_env();
    let expr = Expr::nat_lit(42);
    let instrs = lower_expr(&expr, &env).expect("should lower nat literal");
    // A bare literal doesn't generate instructions (just returns an arg)
    assert!(
        instrs.is_empty(),
        "bare literal should produce no instructions, got: {:?}",
        instrs
    );
}

#[test]
fn test_lower_string_literal() {
    let env = empty_env();
    let expr = Expr::str_lit("hello");
    let instrs = lower_expr(&expr, &env).expect("should lower string literal");
    assert!(
        instrs.is_empty(),
        "bare string literal should produce no instructions"
    );
}

// ---------------------------------------------------------------------------
// lower_expr tests (function call)
// ---------------------------------------------------------------------------

#[test]
fn test_lower_function_call_emits_call_instr() {
    let env = empty_env();
    // Build: UInt32.add 10 20
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("UInt32.add"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(20),
    );
    // App lowering emits a Call instruction with the function name
    let instrs = lower_expr(&expr, &env).expect("should lower function application");
    assert_eq!(instrs.len(), 1, "should emit exactly one Call instruction");
    assert_eq!(instrs[0].op, NativeOp::Call("UInt32.add".to_owned()));
    assert_eq!(instrs[0].args.len(), 2);
    assert_eq!(instrs[0].args[0], NativeArg::LitInt(10));
    assert_eq!(instrs[0].args[1], NativeArg::LitInt(20));
    assert!(
        instrs[0].target.is_some(),
        "Call should bind a result variable"
    );
}

#[test]
fn test_lower_unknown_bare_constant_fails() {
    let env = empty_env();
    // A bare constant (not applied) that's not in the env should fail
    let expr = Expr::const_(Name::from_string("Unknown.thing"), vec![]);
    let result = lower_expr(&expr, &env);
    assert!(result.is_err(), "unknown bare constant should fail");
    match result.unwrap_err() {
        CodegenError::UnknownConstant(name) => {
            assert_eq!(name, "Unknown.thing");
        }
        other => panic!("expected UnknownConstant, got: {other}"),
    }
}

// ---------------------------------------------------------------------------
// erase_proofs tests
// ---------------------------------------------------------------------------

#[test]
fn test_erase_proofs_sort_becomes_erased() {
    let expr = Expr::sort(Level::zero()); // Prop
    let erased = erase_proofs(&expr);
    match erased.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), LC_ERASED);
        }
        other => panic!("expected Const(lcErased), got: {other:?}"),
    }
}

#[test]
fn test_erase_proofs_type_sort_becomes_erased() {
    let expr = Expr::type_(); // Type 1
    let erased = erase_proofs(&expr);
    match erased.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), LC_ERASED);
        }
        other => panic!("expected Const(lcErased), got: {other:?}"),
    }
}

#[test]
fn test_erase_proofs_nat_literal_unchanged() {
    let expr = Expr::nat_lit(42);
    let erased = erase_proofs(&expr);
    assert_eq!(erased, expr, "Nat literals should not be erased");
}

#[test]
fn test_erase_proofs_const_unchanged() {
    let expr = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let erased = erase_proofs(&expr);
    assert_eq!(erased, expr, "Constants should not be erased");
}

#[test]
fn test_erase_proofs_app_recurses() {
    // App(Sort(0), nat_lit(1)) -> App(lcErased, nat_lit(1))
    let expr = Expr::app(Expr::sort(Level::zero()), Expr::nat_lit(1));
    let erased = erase_proofs(&expr);
    match erased.kind() {
        ExprKind::App(func, arg) => {
            // func should be erased
            assert!(
                matches!(func.kind(), ExprKind::Const(name, _) if name.to_string() == LC_ERASED),
                "function should be erased"
            );
            // arg should be unchanged
            assert!(
                matches!(arg.kind(), ExprKind::Lit(Literal::Nat(_))),
                "argument should be unchanged"
            );
        }
        other => panic!("expected App, got: {other:?}"),
    }
}

#[test]
fn test_erase_proofs_pi_prop_result_erased() {
    // Pi(_, Nat, Prop) -> lcErased (because codomain is Prop)
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::sort(Level::zero()); // Prop = Sort 0
    let expr = Expr::pi(BinderInfo::Default, nat_type, prop);
    let erased = erase_proofs(&expr);
    match erased.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), LC_ERASED);
        }
        other => panic!("expected Const(lcErased), got: {other:?}"),
    }
}

#[test]
fn test_erase_proofs_lam_recurses_into_body() {
    // Lam(_, Sort(0), nat_lit(1)) -> Lam(_, lcErased, nat_lit(1))
    let sort0 = Expr::sort(Level::zero());
    let body = Expr::nat_lit(1);
    let expr = Expr::lam(BinderInfo::Default, sort0, body);
    let erased = erase_proofs(&expr);
    match erased.kind() {
        ExprKind::Lam(_, ty, body) => {
            assert!(
                matches!(ty.kind(), ExprKind::Const(name, _) if name.to_string() == LC_ERASED),
                "lambda type should be erased"
            );
            assert!(
                matches!(body.kind(), ExprKind::Lit(Literal::Nat(_))),
                "lambda body should be unchanged"
            );
        }
        other => panic!("expected Lam, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// CodegenError display tests
// ---------------------------------------------------------------------------

#[test]
fn test_codegen_error_unsupported_expr_display() {
    let err = CodegenError::UnsupportedExpr("some form".to_owned());
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported expression"),
        "error message should describe the issue: {msg}"
    );
}

#[test]
fn test_codegen_error_unknown_constant_display() {
    let err = CodegenError::UnknownConstant("Foo.bar".to_owned());
    let msg = format!("{err}");
    assert!(
        msg.contains("Foo.bar"),
        "error should contain the constant name: {msg}"
    );
}

#[test]
fn test_codegen_error_unsupported_type_display() {
    let err = CodegenError::UnsupportedType("Complex".to_owned());
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported type"),
        "error should describe type issue: {msg}"
    );
}

#[test]
fn test_codegen_error_unerased_proof_display() {
    let err = CodegenError::UnerasedProof("proof_term".to_owned());
    let msg = format!("{err}");
    assert!(
        msg.contains("unerased proof"),
        "error should mention unerased proof: {msg}"
    );
}
