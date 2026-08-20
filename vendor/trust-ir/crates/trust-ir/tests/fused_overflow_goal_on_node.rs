// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// FUSION (design 2026-06-20-fusion-obligation-as-clean-expr), OVERFLOW kind
// end-to-end. This is the trust-ir-native successor to
// clean-reflect/tests/fused_overflow.rs: the obligation is no longer DERIVED in
// a bridge at test time — it is a `clean_kernel::Expr` carried ON the node as
// `ProofAnnotation::Goal`, materialized in the SAME builder chain that stamps
// the `NoOverflow` safety marker, by `clean_expr_lowering::overflow_obligation`.
//
// The tests read the goal OFF the node and kernel-discharge it via
// `clean_kernel`'s `TypeChecker::check_type` under `Environment::with_prelude()`
// — the same gate trust-certify uses — with no external `.lean`. A
// change-coupling test mutates `ty` (U8 -> U64) before lowering and asserts the
// on-node goal Expr changes and the verdict flips.
//
// Gated on `clean-expr` (the whole file is `#![cfg(feature = "clean-expr")]`)
// so it only compiles/runs when the typed-proof feature is enabled.
#![cfg(feature = "clean-expr")]

use clean_kernel::{BigNat, Environment, Expr, Level, LocalContext, Name, TypeChecker};
use trust_ir::clean_expr_lowering::overflow_obligation;
use trust_ir::{
    BlockId, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, OverflowOp,
    ProofAnnotation, Ty, ValueId,
};

// --- The LOWERING builder chain (the producer) ------------------------------

/// Lower an `Inst::Overflow` exactly as the trust-ir-bridge site does, but with
/// the fusion addition: in the SAME builder chain that stamps `NoOverflow`, also
/// stamp `ProofAnnotation::Goal` built from the node's OWN fields via
/// `overflow_obligation`. This mirrors lower.rs ~11297 (`InstrNode::new(...)
/// .with_result(..).with_result(..).with_proof(NoOverflow)`), feature-gated.
fn lower_overflow_node(
    op: OverflowOp,
    ty: Ty,
    lhs: ValueId,
    rhs: ValueId,
    operands: (u64, u64),
) -> InstrNode {
    let obligation = overflow_obligation(op, ty.clone(), lhs, rhs, operands)
        .expect("u-typed add-overflow has a representable goal");
    InstrNode::new(Inst::Overflow { op, ty, lhs, rhs })
        .with_result(ValueId::new(2))
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::Goal(Box::new(obligation)))
}

/// The `add_u8` fixture lowered into a real `Module`, proving the node is a
/// genuine trust-ir object reachable through the real container types and
/// carrying its goal as a field.
fn overflow_fixture_module(operands: (u64, u64)) -> Module {
    let mut module = Module::new("fused_goal_on_node");
    module.func_types.push(FuncTy {
        params: vec![Ty::U8],
        returns: vec![Ty::U8],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "add_u8", FuncTyId::new(0), BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U8));
    block.body.push(lower_overflow_node(
        OverflowOp::AddOverflow,
        Ty::U8,
        ValueId::new(0),
        ValueId::new(1),
        operands,
    ));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

// --- Read the goal OFF the node ---------------------------------------------

/// Pull the `ExprObligation` carried as `ProofAnnotation::Goal` off the node.
fn goal_on_node(node: &InstrNode) -> &trust_ir::ExprObligation {
    node.proofs
        .iter()
        .find_map(|p| match p {
            ProofAnnotation::Goal(ob) => Some(ob.as_ref()),
            _ => None,
        })
        .expect("node must carry a ProofAnnotation::Goal")
}

// --- INTRINSIC DISCHARGE: the kernel checks the node's OWN goal --------------

/// A hand-supplied proof term `@Eq.refl Bool Bool.false`, as in fused_overflow.
/// Proves the no-overflow goal exactly when the goal's overflow Bool reduces to
/// `Bool.false` — the kernel does the reduction itself.
fn refl_false() -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), Expr::const_str("Bool.false")],
    )
}

/// Kernel-discharge the node's own goal: build the local context from the
/// obligation's node-sourced hypotheses, then `check_type(term, &goal)` under
/// `Environment::with_prelude()` ONLY. Returns true iff the kernel accepts.
fn discharge(ob: &trust_ir::ExprObligation, proof_term: &Expr) -> bool {
    let env = Environment::with_prelude();
    let mut ctx = LocalContext::new();
    for (name, ty) in &ob.hypotheses {
        ctx.push(
            Name::from_string(name),
            ty.clone(),
            clean_kernel::BinderInfo::Default,
        );
    }
    let tc = TypeChecker::with_context(&env, ctx);
    tc.check_type(proof_term, &ob.goal).is_ok()
}

// --- Tests ------------------------------------------------------------------

#[test]
fn test_goal_is_resident_on_the_real_node() {
    // The node comes through the REAL module container and carries BOTH the
    // cheap NoOverflow marker AND the typed Goal in the same `proofs` Vec.
    let module = overflow_fixture_module((254, 1));
    let node = &module.functions[0].blocks[0].body[0];

    assert!(node.proofs.contains(&ProofAnnotation::NoOverflow));
    let ob = goal_on_node(node);

    // The goal Expr is a FUNCTION of the node: head `Nat.ble`, modulus = U8 256.
    // goal = @Eq Bool (Nat.ble 256 (Nat.add 254 1)) Bool.false
    let eq_args = ob.goal.get_app_args();
    // @Eq Bool <overflow-bool> Bool.false
    let overflow_bool = eq_args[1];
    let ble_args = overflow_bool.get_app_args();
    assert_eq!(ble_args.len(), 2, "Nat.ble takes (modulus, sum)");
    assert_eq!(
        ble_args[0],
        &Expr::nat_lit(256),
        "U8 modulus on the on-node goal must be 2^8 = 256"
    );
}

#[test]
fn test_intrinsic_discharge_u8_no_overflow_is_proven() {
    // U8, 254 + 1 = 255 < 256: the on-node goal kernel-discharges (PROVEN).
    let module = overflow_fixture_module((254, 1));
    let node = &module.functions[0].blocks[0].body[0];
    let ob = goal_on_node(node);
    assert!(
        discharge(ob, &refl_false()),
        "U8 254+1 does not overflow: the kernel must discharge the on-node goal"
    );
}

#[test]
fn test_intrinsic_discharge_u8_overflow_is_unverified() {
    // U8, 255 + 1 = 256 >= 256: the on-node goal is REFUSED (fail closed).
    let module = overflow_fixture_module((255, 1));
    let node = &module.functions[0].blocks[0].body[0];
    let ob = goal_on_node(node);
    assert!(
        !discharge(ob, &refl_false()),
        "U8 255+1 overflows: the kernel must REFUSE the on-node goal"
    );
}

#[test]
fn test_change_coupling_widen_u8_to_u64() {
    // CHANGE-COUPLING: mutate `ty` U8 -> U64 BEFORE lowering, FIXED operands
    // 255 + 1. Both the on-node goal Expr AND the verdict move — because the
    // goal is materialized from the node's own `ty` in the lowering chain.
    let operands = (255, 1);

    // U8: modulus 256; 255+1 = 256 >= 256 => overflow => UNVERIFIED.
    let node_u8 = lower_overflow_node(
        OverflowOp::AddOverflow,
        Ty::U8,
        ValueId::new(0),
        ValueId::new(1),
        operands,
    );
    let ob_u8 = goal_on_node(&node_u8).clone();
    assert_eq!(
        ob_u8.goal.get_app_args()[1].get_app_args()[0],
        &Expr::nat_lit(256),
        "U8 on-node goal modulus is 2^8"
    );
    assert!(
        !discharge(&ob_u8, &refl_false()),
        "U8 255+1 overflows => UNVERIFIED"
    );

    // U64: modulus 2^64; 255+1 = 256 < 2^64 => no overflow => PROVEN.
    let node_u64 = lower_overflow_node(
        OverflowOp::AddOverflow,
        Ty::U64,
        ValueId::new(0),
        ValueId::new(1),
        operands,
    );
    let ob_u64 = goal_on_node(&node_u64).clone();
    assert_ne!(
        ob_u8.goal, ob_u64.goal,
        "the on-node goal Expr is change-coupled: widening `ty` changed the modulus"
    );
    assert_eq!(
        ob_u64.goal.get_app_args()[1].get_app_args()[0],
        &Expr::bignat_lit(BigNat::from_limbs(vec![0, 1])),
        "U64 on-node goal modulus is 2^64"
    );
    assert!(
        discharge(&ob_u64, &refl_false()),
        "U64 255+1 does not overflow => PROVEN: verdict flipped with the type edit"
    );
}

#[test]
fn test_change_coupling_add_to_sub_fails_closed() {
    // CHANGE-COUPLING (op change). The overflow encoder only mints the add goal;
    // a sub-shaped node fails closed at lowering rather than reusing the add
    // goal — the typed analogue of fused_overflow's test_change_coupling_add_to_sub.
    let add = overflow_obligation(
        OverflowOp::AddOverflow,
        Ty::U8,
        ValueId::new(0),
        ValueId::new(1),
        (254, 1),
    );
    assert!(add.is_ok(), "add-overflow has a representable goal");

    let sub = overflow_obligation(
        OverflowOp::SubOverflow,
        Ty::U8,
        ValueId::new(0),
        ValueId::new(1),
        (254, 1),
    );
    assert!(
        sub.is_err(),
        "changing op Add -> Sub must re-shape the obligation, not reuse the add goal"
    );
}
