// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- Instance name correctness tests ---

#[test]
fn test_mk_lt_produces_correct_instance_name_int() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let result = mk_lt(&Sort::Int, &a, &b);
    assert!(
        expr_contains_const(&result, "instLTInt"),
        "mk_lt for Int should use instLTInt, not instLT"
    );
}

#[test]
fn test_mk_le_produces_correct_instance_name_int() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let result = mk_le(&Sort::Int, &a, &b);
    assert!(
        expr_contains_const(&result, "instLEInt"),
        "mk_le for Int should use instLEInt, not instLE"
    );
}

#[test]
fn test_mk_add_produces_correct_instance_name_int() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let result = mk_add(&Sort::Int, &a, &b);
    assert!(
        expr_contains_const(&result, "instHAddInt"),
        "mk_add for Int should use instHAddInt, not instHAdd"
    );
}

#[test]
fn test_mk_mul_produces_correct_instance_name_int() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let result = mk_mul(&Sort::Int, &a, &b);
    assert!(
        expr_contains_const(&result, "instHMulInt"),
        "mk_mul for Int should use instHMulInt, not instHMul"
    );
}

#[test]
fn test_mk_neg_produces_correct_instance_name_int() {
    let a = Expr::fvar(FVarId::new(1));
    let result = mk_neg(&Sort::Int, &a);
    assert!(
        expr_contains_const(&result, "instNegInt"),
        "mk_neg for Int should use instNegInt, not instNeg"
    );
}

// --- Arithmetic chain step sort safety tests ---

#[test]
fn test_mk_chain_step_for_sort_int_supports_all_cmp_op_pairs() {
    let cases = [
        (CmpOp::Le, CmpOp::Le, "Int.le_trans"),
        (CmpOp::Le, CmpOp::Lt, "Int.lt_of_le_of_lt"),
        (CmpOp::Lt, CmpOp::Le, "Int.lt_of_lt_of_le"),
        (CmpOp::Lt, CmpOp::Lt, "Int.lt_trans"),
    ];
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let c = Expr::fvar(FVarId::new(3));
    let h1 = Expr::fvar(FVarId::new(10));
    let h2 = Expr::fvar(FVarId::new(11));

    for (left_op, right_op, expected_const) in cases {
        let result = mk_chain_step_for_sort(&Sort::Int, &a, &b, &c, left_op, right_op, &h1, &h2)
            .expect("Int sort should produce a chain step for every cmp-op pair");
        assert!(
            expr_contains_const(&result, expected_const),
            "Int {left_op:?}+{right_op:?} should use {expected_const}"
        );
    }
}

#[test]
fn test_mk_chain_step_for_sort_real_supports_all_cmp_op_pairs() {
    let cases = [
        (CmpOp::Le, CmpOp::Le, "Real.le_trans"),
        (CmpOp::Le, CmpOp::Lt, "Real.lt_of_le_of_lt"),
        (CmpOp::Lt, CmpOp::Le, "Real.lt_of_lt_of_le"),
        (CmpOp::Lt, CmpOp::Lt, "Real.lt_trans"),
    ];
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let c = Expr::fvar(FVarId::new(3));
    let h1 = Expr::fvar(FVarId::new(10));
    let h2 = Expr::fvar(FVarId::new(11));

    for (left_op, right_op, expected_const) in cases {
        let result = mk_chain_step_for_sort(&Sort::Real, &a, &b, &c, left_op, right_op, &h1, &h2)
            .expect("Real sort should produce a chain step for every cmp-op pair");
        assert!(
            expr_contains_const(&result, expected_const),
            "Real {left_op:?}+{right_op:?} should use {expected_const}"
        );
    }
}

#[test]
fn test_mk_chain_step_for_sort_bool_returns_none() {
    // Bool is not an arithmetic sort — chain steps would be ill-typed.
    // Before the fix, this silently used Nat chain steps.
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let c = Expr::fvar(FVarId::new(3));
    let h1 = Expr::fvar(FVarId::new(10));
    let h2 = Expr::fvar(FVarId::new(11));
    let result = mk_chain_step_for_sort(&Sort::Bool, &a, &b, &c, CmpOp::Le, CmpOp::Le, &h1, &h2);
    assert!(
        result.is_none(),
        "Bool sort must return None — chain steps are only valid for arithmetic sorts"
    );
}

#[test]
fn test_mk_chain_step_for_sort_string_returns_none() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let c = Expr::fvar(FVarId::new(3));
    let h1 = Expr::fvar(FVarId::new(10));
    let h2 = Expr::fvar(FVarId::new(11));
    let result = mk_chain_step_for_sort(&Sort::String, &a, &b, &c, CmpOp::Le, CmpOp::Le, &h1, &h2);
    assert!(
        result.is_none(),
        "String sort must return None for chain steps"
    );
}

#[test]
fn test_mk_chain_step_for_sort_uninterpreted_returns_none() {
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let c = Expr::fvar(FVarId::new(3));
    let h1 = Expr::fvar(FVarId::new(10));
    let h2 = Expr::fvar(FVarId::new(11));
    let result = mk_chain_step_for_sort(
        &Sort::Uninterpreted("MySort".to_string()),
        &a,
        &b,
        &c,
        CmpOp::Le,
        CmpOp::Le,
        &h1,
        &h2,
    );
    assert!(
        result.is_none(),
        "Uninterpreted sort must return None for chain steps"
    );
}

// --- ITE translation error path test (#2400 soundness gap) ---

#[test]
fn test_translate_ite_unresolvable_decidable_returns_error() {
    // mk_ite_checked returns None for conditions without a known Decidable instance.
    // The translate_term caller must convert this to ReconstructionError::UnsupportedTerm.
    // This is a soundness-critical path: fabricating a non-existent Decidable instance
    // would produce ill-typed proof terms the kernel would reject.
    let mut terms = TermStore::new();
    let p = terms.mk_var("fvar_1", Sort::Bool);
    // Use p (a plain boolean variable) as the ITE condition — not LT.lt or LE.le,
    // so resolve_decidable_instance returns None.
    let then_val = terms.mk_var("fvar_2", Sort::Int);
    let else_val = terms.mk_var("fvar_3", Sort::Int);
    let ite = terms.mk_ite(p, then_val, else_val);

    let mut map = VariableMapping::new();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), bool_ty);
    map.register_var("fvar_2", Expr::fvar(FVarId::new(2)), int_ty.clone());
    map.register_var("fvar_3", Expr::fvar(FVarId::new(3)), int_ty);

    let mut ctx = ReconstructionContext::new(&terms, &map, 0);
    let result = ctx.translate_term(ite);
    assert!(
        result.is_err(),
        "ITE with unresolvable Decidable instance should return Err, not fabricate an instance"
    );
    let err = result.unwrap_err();
    let err_msg = format!("{:?}", err);
    assert!(
        err_msg.contains("Decidable") || err_msg.contains("UnsupportedTerm"),
        "error should mention Decidable or UnsupportedTerm, got: {err_msg}"
    );
}

#[test]
fn test_downcast_real_hyp_to_int_recurses_nested_real_add_tree() {
    let mk_real_ofnat = |n| {
        Expr::app(
            Expr::const_(Name::from_string("Real.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let mk_real_ofint =
        |inner: Expr| Expr::app(Expr::const_(Name::from_string("Real.ofInt"), vec![]), inner);
    let mk_real_add = |a: &Expr, b: &Expr| {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Real.add"), vec![]),
                a.clone(),
            ),
            b.clone(),
        )
    };

    let lhs = mk_real_ofnat(4);
    let x = mk_real_ofint(Expr::const_(Name::from_string("testXI"), vec![]));
    let y = mk_real_ofint(Expr::const_(Name::from_string("testYI"), vec![]));
    let one = mk_real_ofnat(1);
    let nested_rhs = mk_add(&Sort::Real, &mk_real_add(&x, &y), &one);
    let h_real = Expr::fvar(FVarId::new(90));

    let (lhs_int, rhs_int, h_int) = downcast_real_hyp_to_int(CmpOp::Le, &lhs, &nested_rhs, &h_real)
        .expect("nested Real.add/HAdd endpoint should downcast recursively to Int");

    assert!(
        expr_contains_const(&lhs_int, "Int.ofNat"),
        "Real.ofNat lhs should normalize to Int.ofNat"
    );
    assert!(
        expr_contains_const(&rhs_int, "Int.add"),
        "nested Real sum should normalize to a nested Int.add tree"
    );
    assert!(
        expr_contains_const(&h_int, "Real.ofInt_add"),
        "recursive downcast proof should transport through Real.ofInt_add"
    );
    assert!(
        expr_contains_const(&h_int, "Real.ofNat_eq_ofInt"),
        "recursive downcast proof should normalize Real.ofNat leaves"
    );
    assert!(
        expr_contains_const(&h_int, "Real.ofInt_le_to_Int"),
        "recursive downcast proof must finish with the Real→Int order bridge"
    );
}

// --- combine_ops tests (untested arithmetic chain combinator) ---

#[test]
fn test_combine_ops_le_le_gives_le() {
    assert_eq!(combine_ops(CmpOp::Le, CmpOp::Le), CmpOp::Le);
}

#[test]
fn test_combine_ops_le_lt_gives_lt() {
    assert_eq!(combine_ops(CmpOp::Le, CmpOp::Lt), CmpOp::Lt);
}

#[test]
fn test_combine_ops_lt_le_gives_lt() {
    assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Le), CmpOp::Lt);
}

#[test]
fn test_combine_ops_lt_lt_gives_lt() {
    assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Lt), CmpOp::Lt);
}
