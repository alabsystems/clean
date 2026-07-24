// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the SCALABLE inductive machine-vs-IR bit-vector add fidelity.
//!
//! The headline theorem `addRec_eq_ir : ∀ xs ys c, addRecM xs ys c = addRecIr
//! xs ys c` is PARAMETRIC in width (the `∀ xs` ranges over all list lengths), so
//! a single kernel theorem covers widths 8/16/32/64 at once. These tests enforce
//! the non-vacuity guard and instantiate the theorem at real widths.

use super::names;
use crate::name::Name;
use crate::{ConstantKind, Environment, Expr, Level, TypeChecker};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_inductive()
        .expect("init_bv_inductive must register + kernel-check");
    env.init_bv_inductive().expect("idempotent");
    env
}

fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn list_bool() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        bool_ty(),
    )
}
fn nil() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        bool_ty(),
    )
}
fn cons(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [bool_ty(), h, t],
    )
}
/// A LSB-first `List Bool` literal of `width` bits from `value`.
fn bv_lit(value: u64, width: u32) -> Expr {
    let mut acc = nil();
    for k in (0..width).rev() {
        let bit = if (value >> k) & 1 == 1 {
            btrue()
        } else {
            bfalse()
        };
        acc = cons(bit, acc);
    }
    acc
}
fn add_rec_m(xs: Expr, ys: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ADD_REC_M), [xs, ys, c])
}
fn add_rec_ir(xs: Expr, ys: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ADD_REC_IR), [xs, ys, c])
}
fn eq_list(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_bool(), x, y],
    )
}
fn eq_refl_list(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [list_bool(), v],
    )
}

fn domain_axioms(env: &Environment, name: &str) -> Vec<String> {
    let mut v: Vec<String> = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    v.sort();
    v
}

#[test]
fn test_inductive_fidelity_is_proved_theorem_with_empty_axiom_closure() {
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::ADD_REC_EQ_IR))
        .expect("addRec_eq_ir must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "addRec_eq_ir must be a PROVED Theorem (kernel-checked by induction)"
    );
    assert!(
        domain_axioms(&env, names::ADD_REC_EQ_IR).is_empty(),
        "addRec_eq_ir must carry ZERO domain axioms; got {:?}",
        domain_axioms(&env, names::ADD_REC_EQ_IR)
    );
}

#[test]
fn test_machine_and_ir_adders_are_distinct_definitions() {
    // NON-VACUITY (1): addRecM/addRecIr and their gates are separate Definitions.
    let env = env();
    for op in [
        names::ADD_REC_M,
        names::ADD_REC_IR,
        names::XOR3,
        names::XOR3_IR,
        names::MAJ,
        names::MAJ_IR,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} must be registered"));
        assert_eq!(info.kind, ConstantKind::Definition, "{op} is a Definition");
    }
    assert_ne!(names::ADD_REC_M, names::ADD_REC_IR);
}

#[test]
fn test_inductive_fidelity_instantiates_at_width_8() {
    // The PARAMETRIC theorem covers width 8: instantiate `addRec_eq_ir` at two
    // symbolic-free 8-bit lists is not needed — we exercise a ground 8-bit add and
    // confirm both adders compute the same value via the theorem's instance.
    // Here: 0b1011_0110 (182) + 0b0100_1001 (73) = 255 at width 8.
    let env = env();
    let x = bv_lit(0b1011_0110, 8);
    let y = bv_lit(0b0100_1001, 8);
    // The theorem instance: addRec_eq_ir x y false : Eq (addRecM x y false) (addRecIr x y false)
    let thm = Expr::apps(
        Expr::const_str(names::ADD_REC_EQ_IR),
        [x.clone(), y.clone(), bfalse()],
    );
    let expected = eq_list(
        add_rec_m(x.clone(), y.clone(), bfalse()),
        add_rec_ir(x, y, bfalse()),
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&thm, &expected)
        .expect("addRec_eq_ir instantiates at a width-8 add and kernel-checks");
}

#[test]
fn test_inductive_fidelity_instantiates_at_width_32() {
    // Width 32 — a real i32 width — by the SAME parametric theorem (no re-proof).
    let env = env();
    let x = bv_lit(0xDEAD_BEEF, 32);
    let y = bv_lit(0x0123_4567, 32);
    let thm = Expr::apps(
        Expr::const_str(names::ADD_REC_EQ_IR),
        [x.clone(), y.clone(), bfalse()],
    );
    let expected = eq_list(
        add_rec_m(x.clone(), y.clone(), bfalse()),
        add_rec_ir(x, y, bfalse()),
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&thm, &expected)
        .expect("addRec_eq_ir instantiates at a width-32 add and kernel-checks");
}

#[test]
fn test_inductive_fidelity_symbolic_goal_not_closeable_by_refl() {
    // NON-VACUITY (2, make-or-break): over SYMBOLIC operands the goal
    // `addRecM xs ys c = addRecIr xs ys c` does NOT close by Eq.refl — the two
    // adders are different terms the kernel does not reduce to a common form
    // without induction. (If a bare refl closed it, the layer would be a
    // rfl-collapse and the theorem vacuous.) We test a CONCRETE width-1 instance
    // with a SYMBOLIC bit, so the gates do not ground-reduce.
    let mut env = env();
    // symbolic bit `sb : Bool`
    env.add_decl(crate::Declaration::Axiom {
        name: Name::from_string("sb"),
        level_params: vec![],
        type_: bool_ty(),
    })
    .expect("sb");
    let sb = Expr::const_str("sb");
    let xs = cons(sb.clone(), nil());
    let ys = cons(sb.clone(), nil());
    // goal: Eq (addRecM xs ys false) (addRecIr xs ys false)
    let lhs = add_rec_m(xs.clone(), ys.clone(), bfalse());
    let rhs = add_rec_ir(xs, ys, bfalse());
    let goal = eq_list(lhs.clone(), rhs);
    // bare refl of LHS would only check under a rfl-collapse.
    let refl = eq_refl_list(lhs);
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&refl, &goal).is_err(),
        "the SYMBOLIC width-1 add equality must NOT close by Eq.refl — if it did, \
         addRecM and addRecIr would be a definitional rfl-collapse and the inductive \
         fidelity theorem would be vacuous"
    );
    // But the THEOREM discharges it (non-vacuous): addRec_eq_ir xs ys false checks.
    let xs2 = cons(sb.clone(), nil());
    let ys2 = cons(sb, nil());
    let thm = Expr::apps(
        Expr::const_str(names::ADD_REC_EQ_IR),
        [xs2.clone(), ys2.clone(), bfalse()],
    );
    let expected = eq_list(
        add_rec_m(xs2.clone(), ys2.clone(), bfalse()),
        add_rec_ir(xs2, ys2, bfalse()),
    );
    tc.check_type(&thm, &expected)
        .expect("the inductive theorem DISCHARGES the symbolic add (non-vacuous)");
}

#[test]
fn test_corrupted_machine_side_makes_fidelity_false() {
    // ADVERSARIAL / SAT-style negative control: a WRONG machine side must make the
    // equality FALSE. We compare the IR adder against a ONE-BIT-MUTATED machine
    // output at a discriminating witness: 1 + 1 at width 2 = [false, true] (=2).
    // The IR adder also computes [false, true]. A corrupted "machine" value that
    // flips bit 1 to false ([false, false] = 0) must NOT be provably equal — a
    // bare Eq.refl against the IR result fails.
    let env = env();
    let one2 = bv_lit(1, 2);
    let ir_sum = add_rec_ir(one2.clone(), one2.clone(), bfalse()); // = [false, true]
    let corrupted = cons(bfalse(), cons(bfalse(), nil())); // [false,false] = 0 (bit1 flipped)
    let false_goal = eq_list(ir_sum.clone(), corrupted.clone());
    let refl = eq_refl_list(ir_sum);
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&refl, &false_goal).is_err(),
        "a one-bit-mutated (bit1 dropped) sum must NOT be provably equal to the IR \
         adder's 1+1=2 result — the kernel must reject the false equality"
    );
}

#[test]
fn test_inductive_proof_genuinely_uses_the_gate_equality_lemmas() {
    // NON-DEGENERACY: the inductive proof must DISCHARGE the per-bit gate
    // difference — i.e. its proof term references `maj_eq_ir` and `xor3_eq_ir`. If
    // it closed without them, the machine and IR adders would be definitionally
    // equal (a rfl-collapse) and the theorem vacuous. We confirm the registered
    // theorem value mentions both lemmas.
    let env = env();
    let info = env
        .get_const(&Name::from_string(names::ADD_REC_EQ_IR))
        .expect("registered");
    let value = info.value.as_ref().expect("a Theorem has a proof value");
    let value_dbg = format!("{value:?}");
    assert!(
        value_dbg.contains("maj_eq_ir"),
        "the inductive proof must apply maj_eq_ir (discharging the carry-encoding \
         difference) — else it is a rfl-collapse"
    );
    assert!(
        value_dbg.contains("xor3_eq_ir"),
        "the inductive proof must apply xor3_eq_ir (discharging the sum-encoding \
         difference)"
    );
}

#[test]
fn test_discriminating_witness_one_plus_one_is_two() {
    // The discriminating witness: at width 2, BOTH adders compute 1+1 = 2 =
    // [false, true]. We check each side ι-reduces to that literal (kernel accepts
    // the refl), the dual of the corrupted-rejection above.
    let env = env();
    let one2 = bv_lit(1, 2);
    let two2 = bv_lit(2, 2); // [false, true]
    let tc = TypeChecker::with_mode(&env, env.mode());
    for side in [
        add_rec_m(one2.clone(), one2.clone(), bfalse()),
        add_rec_ir(one2.clone(), one2.clone(), bfalse()),
    ] {
        let goal = eq_list(side, two2.clone());
        let refl = eq_refl_list(two2.clone());
        tc.check_type(&refl, &goal)
            .expect("both adders compute 1+1=2 at width 2");
    }
}
