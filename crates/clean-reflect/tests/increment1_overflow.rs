// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// The crate's exhaustive-dispatch deny, repeated here because each
// integration test is its own crate root (see the header of src/lib.rs).
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! Increment-1 acceptance test: the reflector emits ONE trust-ir
//! arithmetic-overflow obligation `Expr` from the real trust-ir object, and
//! fails closed for every construct outside Fragment-1.
//!
//! # Intrinsic verification, not an outside model
//!
//! The obligation lives IN the trust-ir object and is verified by the Clean
//! kernel proving the object's OWN obligation — `check_type(proof, goal)`, the
//! de Bruijn criterion — NOT by `is_def_eq`-comparing a synthesized `Expr`
//! against a hand-written external `proofs/trust-soundness/
//! overflow_trust_boundary.lean` used as a per-obligation reference model. The
//! runnable end-to-end demonstration of that intrinsic gate, including
//! change-coupling (mutate the object => obligation + verdict both move), lives
//! in `tests/fused_overflow.rs`.
//!
//! The trust-soundness `.lean` survives ONLY as the once-proven meta-soundness
//! theorem `PROVED => safe` over the kernel's verdict; it is NOT opened per
//! obligation. The previous `load_overflow_env` / `is_def_eq(emit, δ-unfolded
//! overflowObligation body)` side-check (the separate-step, outside-model
//! antipattern) has been RETIRED in favour of the intrinsic kernel gate.
//!
//! This file therefore checks the reflector's structural emission contract (one
//! obligation of the right shape, grounded by the real proven lemma name) and
//! the fail-closed behaviour for out-of-Fragment-1 constructs.

use clean_kernel::Expr;
use clean_reflect::{not_fires, reflect_inst, reflect_module, ReflectError, TrustLabel};
use trust_ir::{
    BlockId, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, OverflowOp, Ty, ValueId,
};

/// Build a minimal valid module: one function with a single
/// `Overflow{AddOverflow, U8}` over operands `%0` (a) and `%1` (the constant 1),
/// the `u8 + 1` fixture from spec Increment 1.
fn overflow_fixture() -> Module {
    let mut module = Module::new("inc1");
    let ft = FuncTy {
        params: vec![Ty::U8],
        returns: vec![Ty::U8],
        is_vararg: false,
        abi: None,
    };
    let ftid = FuncTyId::new(0);
    module.func_types.push(ft);

    let mut func = Function::new(FuncId::new(0), "add_u8", ftid, BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U8));
    block.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U8,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn test_reflect_overflow_yields_one_proven_obligation() {
    let module = overflow_fixture();
    let reflected = reflect_module(&module);
    assert_eq!(
        reflected.obligations.len(),
        1,
        "exactly one Fragment-1 obligation expected from the overflow fixture"
    );
    let ob = &reflected.obligations[0];
    assert_eq!(ob.trust, TrustLabel::Proven);
    assert_eq!(
        ob.grounded_by.as_ref().map(|l| l.0.as_str()),
        Some("overflow_op_sound"),
        "overflow arm must be grounded by the REAL proven lemma overflow_op_sound \
         (applies by instantiation at ayAddOverflows a b)"
    );
    assert_eq!(ob.origin.function, "add_u8");
}

#[test]
fn test_reflected_overflow_shape_is_overflow_obligation_of_ay_add_overflows() {
    // The emitted AST must be `overflowObligation (ayAddOverflows %0 %1)` over
    // the REAL Lean Names (overflow_trust_boundary.lean).
    let module = overflow_fixture();
    let reflected = reflect_module(&module);
    let expr = &reflected.obligations[0].obligation_expr;

    // Head is overflowObligation.
    let head = expr.get_app_fn();
    assert!(head.is_const(), "obligation head must be a constant");
    assert_eq!(
        head_const_name(head).as_deref(),
        Some("overflowObligation"),
        "outermost node must be the real proven obligation overflowObligation"
    );

    // Its single argument is `ayAddOverflows %0 %1`.
    let args = expr.get_app_args();
    assert_eq!(args.len(), 1, "overflowObligation is unary (Bool -> Bool)");
    let inner = &args[0];
    let inner_head = inner.get_app_fn();
    assert_eq!(
        head_const_name(inner_head).as_deref(),
        Some("ayAddOverflows"),
        "inner node must be ay's named BV add-overflow trust-boundary primitive"
    );
    let inner_args = inner.get_app_args();
    assert_eq!(
        inner_args.len(),
        2,
        "ayAddOverflows takes the operand pair (Nat -> Nat -> Bool)"
    );
}

#[test]
fn test_not_fires_wraps_obligation_as_a_well_formed_goal() {
    // The `not_fires` wrapper turns an obligation condition into the
    // `@Eq Bool obligation Bool.false` goal proposition — the negation the
    // kernel discharges. Structural check: head is `Eq`, three args, the
    // obligation in the middle and `Bool.false` last. (The full intrinsic
    // kernel discharge is exercised in `tests/fused_overflow.rs`.)
    let module = overflow_fixture();
    let reflected = reflect_module(&module);
    let emit = reflected.obligations[0].obligation_expr.clone();

    let goal = not_fires(&emit);
    let head = goal.get_app_fn();
    assert_eq!(
        head_const_name(head).as_deref(),
        Some("Eq"),
        "not_fires goal head must be propositional equality"
    );
    let args = goal.get_app_args();
    assert_eq!(args.len(), 3, "@Eq carrier lhs rhs");
    assert_eq!(args[1], &emit, "middle arg is the obligation condition");
    assert_eq!(
        head_const_name(args[2]).as_deref(),
        Some("Bool.false"),
        "the obligation must not fire: it equals Bool.false"
    );
}

// --- Fail-closed: constructs outside Fragment-1 are NOT emitted ------------

#[test]
fn test_branching_construct_is_skipped_fail_closed() {
    // A module whose only instructions are control flow yields ZERO obligations
    // (fail-closed: never a wrong/placeholder Expr).
    let mut module = Module::new("branchy");
    let ftid = FuncTyId::new(0);
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(FuncId::new(0), "br", ftid, BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(0),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");

    let reflected = reflect_module(&module);
    assert!(
        reflected.obligations.is_empty(),
        "branching is out of Fragment-1: no obligation may be emitted"
    );
}

#[test]
fn test_reflect_inst_branch_returns_unsupported() {
    // The per-instruction dispatch fails closed (Unsupported) for an out-of-
    // Fragment-1 construct rather than emitting a shape.
    let branch = Inst::CondBr {
        cond: ValueId::new(0),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    };
    match reflect_inst(&branch) {
        Err(ReflectError::Unsupported { construct }) => {
            assert!(
                construct.contains("branching") || construct.contains("CondBr"),
                "unsupported label should name the construct, got: {construct}"
            );
        }
        other => panic!("expected Err(Unsupported), got {other:?}"),
    }
}

#[test]
fn test_reflect_inst_div_returns_unsupported() {
    // BinOp div is Increment 2, NOT yet in the emission contract: fail closed.
    let div = Inst::BinOp {
        op: trust_ir::BinOp::UDiv,
        ty: Ty::U8,
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    };
    assert!(
        matches!(reflect_inst(&div), Err(ReflectError::Unsupported { .. })),
        "div is not in the Increment-1 emission contract; must fail closed"
    );
}

#[test]
fn test_reflect_inst_drop_returns_unsupported_by_name() {
    // trust-ir v47 `Inst::Drop` runs a destructor: observable, so it is never
    // read as a no-op. The dispatch refuses it by NAME, not through a
    // catch-all label.
    let drop = Inst::Drop {
        ty: Ty::U8,
        ptr: ValueId::new(0),
    };
    match reflect_inst(&drop) {
        Err(ReflectError::Unsupported { construct }) => {
            assert!(
                construct.contains("Drop") && construct.contains("v47"),
                "the refusal should name the Drop construct, got: {construct}"
            );
        }
        other => panic!("expected Err(Unsupported), got {other:?}"),
    }
}

#[test]
fn test_reflect_inst_array_splat_returns_unsupported_by_name_at_any_length() {
    // trust-ir v50 `Inst::ArraySplat`: `n` copies of one register. Fragment-1
    // has no array term, so the dispatch refuses it by NAME. The refusal reads
    // only the variant, so a one-lane array and a `u64::MAX`-lane array get the
    // same answer (a dispatch that walked the lanes would not return from the
    // second).
    let splat = |len| Inst::ArraySplat {
        ty: Ty::Array(trust_ir::TyId::new(0), len),
        value: ValueId::new(0),
    };
    let refusal = |inst: &Inst| match reflect_inst(inst) {
        Err(ReflectError::Unsupported { construct }) => construct,
        other => panic!("expected Err(Unsupported), got {other:?}"),
    };
    let (small, huge) = (refusal(&splat(1)), refusal(&splat(u64::MAX)));
    assert!(
        small.contains("ArraySplat") && small.contains("v50"),
        "the refusal should name the ArraySplat construct, got: {small}"
    );
    assert_eq!(small, huge, "the refusal must not depend on the lane count");
}

fn head_const_name(e: &Expr) -> Option<String> {
    use clean_kernel::ExprKind;
    if let ExprKind::Const(name, _) = e.kind() {
        Some(name.to_string())
    } else {
        None
    }
}
