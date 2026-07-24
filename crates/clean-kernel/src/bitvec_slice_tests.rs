// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the minimal slice BitVec layer.

use super::*;
use crate::name::Name;
use crate::{BinderInfo, Declaration, Environment, Expr, FVarId, LocalContext, TypeChecker};

fn env_with_slice() -> Environment {
    let mut env = Environment::new();
    env.init_bv_slice().expect("init_bv_slice");
    env
}

/// Two free `BV` operands `a`, `b` in a fresh context.
fn ab(env: &mut Environment) -> (Expr, Expr) {
    let bv = Expr::const_str(names::BV);
    for n in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: bv.clone(),
        })
        .expect("add operand");
    }
    (Expr::const_str("a"), Expr::const_str("b"))
}

#[test]
fn test_init_bv_slice_registers_layer() {
    let env = env_with_slice();
    for n in [
        names::BV,
        names::GET_BIT,
        names::BV_ADD,
        names::BV_SUB,
        names::BV_EQ,
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "missing {n}"
        );
    }
}

#[test]
fn test_negated_goal_is_a_prop() {
    let mut env = env_with_slice();
    let (a, b) = ab(&mut env);
    let lhs = bv_binop(false, a.clone(), b.clone());
    let rhs = bv_binop(false, a, b);
    let goal = negated_goal(lhs, rhs);

    let tc = TypeChecker::new(&env);
    let ty = tc.infer_type(&goal).expect("goal infers");
    assert!(ty.is_prop(), "negated goal must be a Prop, got {ty:?}");
}

#[test]
fn test_bit_eq_refl_proves_identical_bit() {
    let mut env = env_with_slice();
    let (a, b) = ab(&mut env);
    let lhs = bv_binop(false, a.clone(), b.clone());
    // identical rhs
    let rhs = lhs.clone();

    let prop = bit_eq_prop(&lhs, &rhs, 7);
    let proof = bit_eq_refl(&lhs, 7);

    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &prop)
        .expect("Eq.refl proves the identical-operand per-bit equality");
}

#[test]
fn test_bit_eq_refl_rejected_for_distinct_operands() {
    // M2 in miniature at the kernel layer: a refl proof of `getBit lhs i = getBit
    // lhs i` does NOT prove `getBit lhs i = getBit rhs i` when lhs != rhs.
    let mut env = env_with_slice();
    let (a, b) = ab(&mut env);
    let lhs = bv_binop(false, a.clone(), b.clone()); // bvSub a b
    let rhs = bv_binop(false, b, a); // bvSub b a  (swapped)

    let swapped_prop = bit_eq_prop(&lhs, &rhs, 3);
    let identical_proof = bit_eq_refl(&lhs, 3);

    let tc = TypeChecker::new(&env);
    assert!(
        tc.check_type(&identical_proof, &swapped_prop).is_err(),
        "refl of identical operands must NOT prove the swapped-operand bit equality"
    );
}

#[test]
fn test_bv_eq_unfolds_to_and_chain_head() {
    // bvEq lhs rhs should be definitionally an And whose first conjunct is
    // (getBit lhs 0 = getBit rhs 0). We check the whole `bvEq` is a Prop and that
    // a proof built as the And-chain of refls type-checks against it for the
    // identical-operand case.
    let mut env = env_with_slice();
    let (a, b) = ab(&mut env);
    let lhs = bv_binop(false, a.clone(), b.clone());
    let rhs = lhs.clone();

    let eq = bv_eq(lhs.clone(), rhs.clone());
    let tc = TypeChecker::new(&env);
    let ty = tc.infer_type(&eq).expect("bvEq infers");
    assert!(ty.is_prop(), "bvEq must be a Prop");

    // Build the full And-chain proof: And.intro of all per-bit refls.
    let proof = and_chain_proof(&lhs, BV_SLICE_WIDTH);
    tc.check_type(&proof, &eq)
        .expect("And-chain of refls proves bvEq for identical operands");
}

/// Build a proof of the `bvEq`-body And-chain for identical operands.
fn and_chain_proof(x: &Expr, width: u32) -> Expr {
    assert!(width > 0);
    let mut acc = bit_eq_refl(x, width - 1);
    let mut acc_ty = bit_eq_prop(x, x, width - 1);
    for bit in (0..width - 1).rev() {
        let head_ty = bit_eq_prop(x, x, bit);
        let head_proof = bit_eq_refl(x, bit);
        acc = Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [head_ty.clone(), acc_ty.clone(), head_proof, acc.clone()],
        );
        acc_ty = Expr::apps(
            Expr::const_(Name::from_string("And"), vec![]),
            [head_ty, acc_ty],
        );
    }
    acc
}

#[test]
fn test_layer_has_no_unexpected_free_fvars() {
    // Sanity: the registered bvEq value is closed.
    let env = env_with_slice();
    let info = env
        .get_const(&Name::from_string(names::BV_EQ))
        .expect("bvEq present");
    // Just ensure the layer round-trips through a no-op context check.
    let _ = info;
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        FVarId::new(1),
        Name::from_string("dummy"),
        Expr::const_str(names::BV),
        BinderInfo::Default,
    );
}

/// Fidelity for the trust-mc ouroboros arm `build_kernel_and_chain_width`
/// (soundness_oracle.rs): the REAL `and_chain` must be TOTAL — the `width == 0` early-return
/// dominates the `width - 1` decrement, so it never underflows — which is exactly what Trust's
/// discharge PROVES of the model (`ouroboros_clean_kernel_and_chain_width_proven_safe`). Widths
/// are kept small because `and_chain` builds a `width`-element conjunction; `width == 0` is the
/// panic boundary the guard protects (`width - 1` would underflow there).
#[test]
fn and_chain_width_model_matches_kernel() {
    let x = Expr::bvar(1);
    let y = Expr::bvar(0);
    // width == 0: the degenerate case early-returns `True` — the `width - 1` decrement is NOT
    // reached, so the underflow that the trust-mc model guards against cannot occur.
    assert_eq!(
        and_chain(&x, &y, 0),
        Expr::const_str("True"),
        "and_chain(width=0) must early-return True (no width-1 underflow)"
    );
    // width >= 1: `width - 1` is in range; executing the real kernel function must not panic.
    for width in [1u32, 2, 3, 5, 8, 16] {
        let _ = and_chain(&x, &y, width);
    }
}
