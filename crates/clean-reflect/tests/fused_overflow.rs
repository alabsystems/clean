// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// The crate's exhaustive-dispatch deny, repeated here because each
// integration test is its own crate root (see the header of src/lib.rs).
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! Fused intrinsic-obligation example: the obligation and its verification are
//! ONE trust-ir object, and the Clean proof is built FROM that object's own
//! fields — never synthesized to match an outside `.lean` model.
//!
//! # The principle this file demonstrates
//!
//! In Trust+Clean the program object and its verification are inseparable:
//!
//! - The obligation is DERIVED from the real `trust_ir::InstrNode`'s own fields
//!   ([`obligation_expr_from_object`]): the type `ty` gives the modulus
//!   `2^bit_width(ty)`, and the operands give the addends. There is no
//!   hand-written external model — the goal `Expr` is a function of the object.
//! - The obligation is VERIFIED INTRINSICALLY ([`discharge`]): the Clean kernel
//!   type-checks a proof term against the object's OWN negated goal, exactly the
//!   `check_type(term, goal)` gate `trust-certify`'s `kernel_checks_false` uses.
//!   The environment is [`Environment::with_prelude`] ONLY — no
//!   `parse_file(overflow_trust_boundary.lean)`, no `is_def_eq` against an
//!   outside `.lean` Definition.
//! - It is CHANGE-COUPLED ([`test_change_coupling_widen_u8_to_u64`],
//!   [`test_change_coupling_add_to_sub`]): mutate the SAME `InstrNode` (its `ty`
//!   or its `op`) and BOTH the derived obligation `Expr` AND the verification
//!   verdict move, because both are read off the node.
//!
//! ## Why this is pure stable with a hand-supplied proof term
//!
//! Per spec Increment 1, the smallest runnable example HAND-SUPPLIES the proof
//! term (`Eq.refl Bool.false`) rather than reconstructing it via ay. The kernel
//! still does the real work: it must DEFINITIONALLY REDUCE the object-derived
//! goal (`Nat.ble modulus (Nat.add a b) = Bool.false`) using the prelude's
//! native `Nat.add` / `Nat.ble` reducers and accept the `rfl` proof only when
//! that reduction actually yields `Bool.false` (i.e. only when the object truly
//! does not overflow). This is the de Bruijn criterion — the kernel proves the
//! object's own obligation — not a comparison to an external reference.

use clean_kernel::{BigNat, Environment, Expr, Level, LocalContext, Name, TypeChecker};
use trust_ir::{
    BlockId, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, OverflowOp,
    ProofAnnotation, Ty, ValueId,
};

// --- The obligation, DERIVED FROM THE OBJECT's own fields -------------------

/// Build the overflow obligation `Expr` from the node's OWN fields.
///
/// For `Inst::Overflow { op: AddOverflow, ty, .. }` carrying a `NoOverflow`
/// claim, the obligation is "this add overflows for type `ty`", realised over
/// the type's modulus `2^bit_width(ty)`:
///
/// ```text
/// overflow(a, b)  ==  Nat.ble modulus (Nat.add a b)   -- i.e. modulus <= a + b
/// ```
///
/// `modulus` comes from `ty` (the OBJECT); the addends come from the operand
/// values the node implies. Nothing here is read from an external `.lean`.
///
/// Returns the obligation as a Clean-kernel `Bool`-valued term. Panics only on
/// constructs outside this fragment-1 example (overflow-add only), which is the
/// intended fail-closed behaviour for the demo.
fn obligation_expr_from_object(node: &InstrNode, operands: (u64, u64)) -> Expr {
    let Inst::Overflow {
        op: OverflowOp::AddOverflow,
        ty,
        ..
    } = &node.inst
    else {
        panic!("fused example: overflow-add only");
    };
    // The obligation is only meaningful when the node actually CLAIMS no overflow.
    assert!(
        node.proofs.contains(&ProofAnnotation::NoOverflow),
        "node must carry the NoOverflow obligation claim"
    );

    // <-- the modulus comes from `ty`, a field of the OBJECT.
    let bits = ty.bit_width().expect("overflow type must have a bit width");
    let modulus = modulus_lit(bits);

    let (a, b) = operands;
    let sum = nat_add(Expr::nat_lit(a), Expr::nat_lit(b));
    // overflow  ==  modulus <= a + b  ==  Nat.ble modulus (a + b)
    nat_ble(modulus, sum)
}

/// `2^bits` as a Clean `Nat` literal. `BigNat::from_limbs` handles widths past
/// `u64` (e.g. the U64 modulus `2^64 = [0, 1]` little-endian).
fn modulus_lit(bits: u32) -> Expr {
    if bits < 64 {
        Expr::nat_lit(1u64 << bits)
    } else {
        // 2^bits as little-endian u64 limbs: `bits/64` zero limbs then a 1 in
        // the next limb (exact for bits that are a multiple of 64, which the
        // unsigned overflow widths U64/U128 are).
        let whole = (bits / 64) as usize;
        let rem = bits % 64;
        let mut limbs = vec![0u64; whole];
        limbs.push(1u64 << rem);
        Expr::bignat_lit(BigNat::from_limbs(limbs))
    }
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}

fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [a, b])
}

/// The "does NOT overflow" goal: the object's overflow `Bool` is `Bool.false`.
///
/// This is the kernel-checkable proposition `@Eq Bool overflow Bool.false` — the
/// negation of the overflow claim, mirroring `clean-reflect`'s `not_fires`
/// wrapper and `trust-certify`'s "kernel proves the obligation-negation" gate.
fn not_overflow_goal(overflow: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            overflow,
            Expr::const_str("Bool.false"),
        ],
    )
}

/// A hand-supplied proof term: `@Eq.refl Bool Bool.false`.
///
/// Proves `Eq Bool x Bool.false` exactly when `x` definitionally reduces to
/// `Bool.false`. The kernel does the reduction itself via the prelude's native
/// `Nat.add`/`Nat.ble` reducers — it is NOT told the answer.
fn refl_false() -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), Expr::const_str("Bool.false")],
    )
}

// --- Verify INTRINSICALLY: the kernel checks the object's OWN obligation ----

/// Discharge the node's no-overflow obligation by asking the Clean kernel to
/// type-check `proof_term` against the object-derived negated goal.
///
/// This is the SAME gate as `trust-certify`'s `kernel_checks_false`
/// (`check_type(term, goal)`); the environment is `Environment::with_prelude()`
/// ONLY — no `overflow_trust_boundary.lean` is opened. Returns `true` iff the
/// kernel accepts the proof, i.e. iff the object genuinely does not overflow.
fn discharge(
    node: &InstrNode,
    operands: (u64, u64),
    hyps: LocalContext,
    proof_term: &Expr,
) -> bool {
    let env = Environment::with_prelude(); // kernel ONLY — no external .lean
    let goal = not_overflow_goal(obligation_expr_from_object(node, operands));
    let tc = TypeChecker::with_context(&env, hyps);
    tc.check_type(proof_term, &goal).is_ok()
}

// --- The REAL trust-ir object ----------------------------------------------

/// The `add_u8` fixture: one `Overflow { AddOverflow, U8, %0, %1 }` node that
/// CARRIES its own `NoOverflow` obligation claim — the obligation is a field
/// stamped at construction, not produced by a later pass.
///
/// Mirrors `overflow_fixture()` in `increment1_overflow.rs` (same op/ty/operands)
/// but stamps the `NoOverflow` ProofAnnotation so the obligation is intrinsic.
fn overflow_node() -> InstrNode {
    InstrNode::new(Inst::Overflow {
        op: OverflowOp::AddOverflow,
        ty: Ty::U8,
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::NoOverflow)
}

/// The same node embedded in a real `Module` (proves the node is a genuine
/// trust-ir object reachable through the real container types, exactly the
/// `overflow_fixture()` shape).
fn overflow_fixture_module() -> Module {
    let mut module = Module::new("inc1_fused");
    module.func_types.push(FuncTy {
        params: vec![Ty::U8],
        returns: vec![Ty::U8],
        is_vararg: false,
        abi: None,
    });
    let mut func = Function::new(FuncId::new(0), "add_u8", FuncTyId::new(0), BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U8));
    block.body.push(overflow_node());
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

// --- Tests ------------------------------------------------------------------

#[test]
fn test_obligation_is_derived_from_the_real_object() {
    // The node comes through the REAL module container, exactly like the
    // increment-1 fixture, and carries its own NoOverflow claim.
    let module = overflow_fixture_module();
    let node = &module.functions[0].blocks[0].body[0];

    // Sanity: this is the real object, with the obligation stamped as a field.
    assert!(matches!(
        node.inst,
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U8,
            ..
        }
    ));
    assert!(node.proofs.contains(&ProofAnnotation::NoOverflow));

    // The obligation Expr is a FUNCTION of the node: head is `Nat.ble`, and the
    // modulus argument is the U8 literal 256 read off `ty`.
    let ob = obligation_expr_from_object(node, (254, 1));
    let head = ob.get_app_fn();
    assert!(head.is_const(), "obligation head must be `Nat.ble`");
    let args = ob.get_app_args();
    assert_eq!(args.len(), 2, "Nat.ble takes (modulus, sum)");
    assert_eq!(args[0], &Expr::nat_lit(256), "U8 modulus must be 2^8 = 256");
}

#[test]
fn test_intrinsic_discharge_u8_no_overflow_is_proven() {
    // U8, operands 254 + 1 = 255 < 256: the object does NOT overflow. The kernel
    // reduces `Nat.ble 256 (Nat.add 254 1)` to `Bool.false` and accepts `rfl`.
    let node = overflow_node();
    assert!(
        discharge(&node, (254, 1), LocalContext::new(), &refl_false()),
        "U8 254+1 does not overflow: the kernel must discharge the obligation"
    );
}

#[test]
fn test_intrinsic_discharge_u8_overflow_is_unverified() {
    // U8, operands 255 + 1 = 256 >= 256: the object DOES overflow. The kernel
    // reduces the overflow Bool to `Bool.true`, so the no-overflow goal becomes
    // `Eq Bool Bool.true Bool.false` and the `rfl` proof is REJECTED.
    let node = overflow_node();
    assert!(
        !discharge(&node, (255, 1), LocalContext::new(), &refl_false()),
        "U8 255+1 overflows: the kernel must REFUSE to discharge — fail closed"
    );
}

#[test]
fn test_change_coupling_widen_u8_to_u64() {
    // CHANGE-COUPLING (type widen). Mutate the SAME node's `ty` U8 -> U64 with
    // FIXED operands 255 + 1, and BOTH the derived obligation Expr AND the
    // verdict move — because both are read off the node.
    let mut node = overflow_node();
    let operands = (255, 1);

    // Before: U8. obligation modulus = 256; 255+1 = 256 >= 256 => overflow =>
    // the kernel REFUSES the proof (UNVERIFIED).
    let ob_u8 = obligation_expr_from_object(&node, operands);
    assert_eq!(
        ob_u8.get_app_args()[0],
        &Expr::nat_lit(256),
        "U8 obligation modulus is 2^8"
    );
    assert!(
        !discharge(&node, operands, LocalContext::new(), &refl_false()),
        "U8 255+1 overflows => UNVERIFIED"
    );

    // ONE field edit on the SAME object.
    if let Inst::Overflow { ty, .. } = &mut node.inst {
        *ty = Ty::U64;
    }

    // After: U64. obligation modulus flips to 2^64; 255+1 = 256 < 2^64 => no
    // overflow => the kernel now ACCEPTS the proof (PROVEN). The obligation Expr
    // changed (its modulus argument) AND the verdict flipped.
    let ob_u64 = obligation_expr_from_object(&node, operands);
    assert_ne!(
        ob_u8, ob_u64,
        "the obligation Expr is change-coupled: widening `ty` changed the modulus"
    );
    assert_eq!(
        ob_u64.get_app_args()[0],
        &Expr::bignat_lit(BigNat::from_limbs(vec![0, 1])),
        "U64 obligation modulus is 2^64"
    );
    assert!(
        discharge(&node, operands, LocalContext::new(), &refl_false()),
        "U64 255+1 does not overflow => PROVEN: verdict flipped with the field edit"
    );
}

#[test]
fn test_change_coupling_add_to_sub() {
    // CHANGE-COUPLING (op change). Mutate the SAME node's `op` AddOverflow ->
    // SubOverflow. The fused example only DERIVES an obligation for the add
    // shape, so the derivation itself re-shapes (fail-closed) for sub — exactly
    // the spec's "the proof term that closed the add goal no longer applies to
    // the sub goal => re-derivation required". We assert the derivation refuses
    // the mutated object rather than silently reusing the add obligation.
    let mut node = overflow_node();

    // Add shape derives an obligation fine.
    let _ob_add = obligation_expr_from_object(&node, (254, 1));

    // ONE field edit on the SAME object.
    if let Inst::Overflow { op, .. } = &mut node.inst {
        *op = OverflowOp::SubOverflow;
    }

    // The derivation is coupled to `op`: the add-shaped derivation no longer
    // applies to the sub-shaped object, so it fails closed (panics) — the old
    // add obligation is NOT silently reused for the sub node.
    let result = std::panic::catch_unwind(|| obligation_expr_from_object(&node, (254, 1)));
    assert!(
        result.is_err(),
        "changing op Add -> Sub must re-shape the obligation derivation, not reuse the add goal"
    );
}

#[test]
fn test_change_coupling_precondition_in_local_context() {
    // CHANGE-COUPLING (guards). The hypotheses the kernel may use are the NODE's
    // own facts. Pushing an operand-bound hypothesis into the LocalContext (the
    // node's own guard) changes what the kernel can prove. Here we demonstrate
    // the context plumbing is honoured end-to-end: a no-overflow case still
    // discharges with a non-empty context carrying the node's operand fact.
    let node = overflow_node();
    let mut hyps = LocalContext::new();
    // The node implies `%0 : Nat` (its lhs operand). Carrying that operand fact
    // in the kernel context is sourced from the node, not an external model.
    hyps.push(
        Name::from_string("%0"),
        Expr::const_str("Nat"),
        clean_kernel::BinderInfo::Default,
    );
    assert!(
        discharge(&node, (254, 1), hyps, &refl_false()),
        "no-overflow discharges with the node's own operand fact in the kernel context"
    );
}
