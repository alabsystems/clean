// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the B1 coercion-identity layer.
//!
//! The two parametric identities `extract_zeroext_id` /  `or_zero_id` (and their
//! `bvfEval` liftings) discharge the gate's add@N width-coercion residual WITHOUT
//! any adder proof. These tests enforce the non-vacuity guard: the coercion ops
//! are REAL `List Bool` operations, the identities hold by computation, and
//! MUTATED coercions (wrong pad bit, wrong extract offset/width, nonzero const)
//! BREAK the identity at a discriminating witness and are kernel-REJECTED.

use super::names;
use crate::name::Name;
use crate::{BinderInfo, ConstantKind, Environment, Expr, Level, TypeChecker};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_coercion()
        .expect("init_bv_coercion must register + kernel-check");
    env.init_bv_coercion().expect("idempotent");
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
fn nat_lit(n: u32) -> Expr {
    let mut acc = Expr::const_str("Nat.zero");
    for _ in 0..n {
        acc = Expr::app(Expr::const_str("Nat.succ"), acc);
    }
    acc
}
fn take_len(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::TAKE_LEN), [xs, ys])
}
fn zext(e: Expr, k: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ZEXT), [e, k])
}
fn zip_or(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ZIP_OR), [xs, ys])
}
fn all_false(z: Expr) -> Expr {
    Expr::app(Expr::const_str(names::ALL_FALSE), z)
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
fn test_coercion_identities_are_proved_theorems_with_empty_axiom_closure() {
    let env = env();
    for thm in [
        names::EXTRACT_ZEXT_ID,
        names::BV_TAKE_LEN_APPEND,
        names::OR_ZERO_ID,
        names::ADD_ZERO_ID,
        names::BVF_EXTRACT_ZEXT_ID,
        names::BVF_OR_ZERO_ID,
        names::BVF_ADD_ZERO_ID,
        names::BVF_WRAPPER_ID,
        names::BVF_ADD_CONG,
        names::BVF_SUB_CONG,
        names::BVF_AND_CONG,
        names::BVF_XOR_CONG,
        names::BVF_MUL_CONG,
        names::BVF_OR_CONG2,
        names::BVF_ZEXT_CONG,
        names::BVF_EXTRACT_CONG1,
        names::ITE_VAL_NOT,
        names::BVF_DIV_CONG,
        names::BVF_SDIV_CONG,
        names::BVF_SHL_CONG,
        names::BVF_LSHR_CONG,
        names::BVF_ASHR_CONG,
        names::DIV_GUARD_BRIDGE,
        names::BV_BEQ_REFL,
        names::SELECT_STORE_SAME,
        names::SELECT_STORE_DIFF,
        names::BV_BEQ_CONS_FALSE,
        names::BEQ_EQ_ISZERO_SUB,
        names::EQ_VALUE_BRIDGE,
        names::ULT_VALUE_BRIDGE,
        names::ULE_VALUE_BRIDGE,
        names::DEMORGAN_AND_NOT,
        "Clean.BVC.goalConsCongTrue",
        "Clean.BVC.goalConsCongFalse",
        // #56 telescope-collapse: the slt bridge + its standalone inversion lemmas.
        names::SLT_FLAG_BRIDGE,
        names::SLT_VALUE_BRIDGE,
        names::SLE_VALUE_BRIDGE,
        "Clean.BVC.sltConsCong",
        "Clean.BVC.consOfIsCons",
        "Clean.BVC.isConsOfLenSucc",
        "Clean.BVC.nilOfNotIsCons",
        "Clean.BVC.nilOfLenZero",
    ] {
        let info = env
            .get_const(&Name::from_string(thm))
            .unwrap_or_else(|| panic!("{thm} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{thm} must be a PROVED Theorem"
        );
        assert!(
            domain_axioms(&env, thm).is_empty(),
            "{thm} must carry ZERO domain axioms; got {:?}",
            domain_axioms(&env, thm)
        );
    }
}

#[test]
fn test_coercion_ops_are_real_definitions() {
    let env = env();
    for op in [
        names::APPEND,
        names::REPL_F,
        names::ZEXT,
        names::TAKE_LEN,
        names::ALL_FALSE,
        names::BV_MUL,
        names::BV_TO_NAT,
        names::NAT_TO_BV_AUX,
        names::BV_DIV,
        names::BV_NEG,
        names::BV_ABS,
        names::BV_SDIV,
        names::BV_TWO_POW,
        names::BV_SHL,
        names::BV_LSHR,
        names::BV_ASHR,
        names::ZIP_OR,
        names::BVF_EVAL,
        names::BV_BEQ,
        names::BV_IS_ZERO,
        names::BV_ITE_VAL,
        names::BV_ULT,
        names::BV_ULE,
        names::CARRY_OUT,
        names::BV_FLIP_MSB,
        names::BV_SLT_REAL,
        names::BV_SLE_REAL,
        names::BV_LAST_BIT,
        names::BV_IS_CONS,
        names::BV_LEN,
        names::BV_SELECT,
        names::BV_STORE,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op}"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{op} is a real Definition"
        );
    }
}

/// DIV RUNG 1 — differential validation that `bvDiv` computes REAL unsigned
/// truncating division (the bvUlt lesson: NO non-semantic stub). Each positive
/// case registers `Eq.refl expected : Eq (bvDiv a b) expected`, which the kernel
/// accepts ONLY if `bvDiv a b` REDUCES to `expected` (so the kernel itself is the
/// validator). The negative control proves a WRONG quotient is kernel-REJECTED,
/// so the positive checks are non-vacuous. Covers truncation and the AArch64
/// `UDIV` by-zero = 0 convention (= Lean `Nat.div n/0 = 0`).
#[test]
fn test_bvdiv_is_faithful_real_unsigned_division() {
    let mut env = env();
    let div = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_DIV), [a, b]);
    let mut check = |label: &str, a: Expr, b: Expr, expected: Expr, should_pass: bool| {
        let ty = eq_list(div(a, b), expected.clone());
        let res = env.add_decl(crate::Declaration::Theorem {
            name: Name::from_string(&format!("Clean.BVC.__bvdiv_diff_{label}")),
            level_params: vec![],
            type_: ty,
            value: eq_refl_list(expected),
        });
        assert_eq!(
            res.is_ok(),
            should_pass,
            "bvDiv {label}: expected reduce-pass={should_pass}, got {res:?}"
        );
    };
    // truncating quotients, width 3
    check("6div2_w3", bv_lit(6, 3), bv_lit(2, 3), bv_lit(3, 3), true);
    check("7div2_w3", bv_lit(7, 3), bv_lit(2, 3), bv_lit(3, 3), true);
    check("5div3_w3", bv_lit(5, 3), bv_lit(3, 3), bv_lit(1, 3), true);
    // div-by-zero = 0 (AArch64 UDIV / Lean Nat.div convention)
    check("6div0_w3", bv_lit(6, 3), bv_lit(0, 3), bv_lit(0, 3), true);
    // wider, width 8
    check(
        "100div7_w8",
        bv_lit(100, 8),
        bv_lit(7, 8),
        bv_lit(14, 8),
        true,
    );
    check(
        "200div10_w8",
        bv_lit(200, 8),
        bv_lit(10, 8),
        bv_lit(20, 8),
        true,
    );
    // adversarial edges (universally hand-traced in the substrate verification): div-by-zero,
    // max/1 (worst-case quotient = dividend; dividend width always holds it), b>a, and width-1.
    check("0div0_w3", bv_lit(0, 3), bv_lit(0, 3), bv_lit(0, 3), true);
    check("1div0_w3", bv_lit(1, 3), bv_lit(0, 3), bv_lit(0, 3), true);
    check("7div1_w3", bv_lit(7, 3), bv_lit(1, 3), bv_lit(7, 3), true);
    check("2div5_w3", bv_lit(2, 3), bv_lit(5, 3), bv_lit(0, 3), true);
    check(
        "255div1_w8",
        bv_lit(255, 8),
        bv_lit(1, 8),
        bv_lit(255, 8),
        true,
    );
    check("1div1_w1", bv_lit(1, 1), bv_lit(1, 1), bv_lit(1, 1), true);
    check("0div0_w1", bv_lit(0, 1), bv_lit(0, 1), bv_lit(0, 1), true);
    // NEGATIVE control: 6/2 = 3, NOT 2 — a wrong quotient must be kernel-REJECTED.
    check(
        "6div2_wrong2",
        bv_lit(6, 3),
        bv_lit(2, 3),
        bv_lit(2, 3),
        false,
    );
}

/// DIV RUNG 2 — differential validation that `bvSDiv` computes REAL signed truncating
/// (round-toward-zero) division via sign-magnitude. Width-4 two's-complement vectors;
/// negatives are given as their unsigned bit-pattern (-7=9, -3=13, -2=14, -8=8, -5=11, -1=15).
/// Covers all four sign combinations, round-toward-zero (-8/3 = -2, NOT the floor -3),
/// SDIV-by-zero = 0, and the INT_MIN/-1 overflow (= INT_MIN). The negative control rejects a
/// wrong quotient so the positives are non-vacuous.
#[test]
fn test_bvsdiv_is_faithful_real_signed_division() {
    let mut env = env();
    let sdiv = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_SDIV), [a, b]);
    let mut check = |label: &str, a: Expr, b: Expr, expected: Expr, should_pass: bool| {
        let ty = eq_list(sdiv(a, b), expected.clone());
        let res = env.add_decl(crate::Declaration::Theorem {
            name: Name::from_string(&format!("Clean.BVC.__bvsdiv_diff_{label}")),
            level_params: vec![],
            type_: ty,
            value: eq_refl_list(expected),
        });
        assert_eq!(
            res.is_ok(),
            should_pass,
            "bvSDiv {label}: expected reduce-pass={should_pass}, got {res:?}"
        );
    };
    // four sign combinations (w4): 7/2=3, -7/2=-3, 7/-2=-3, -7/-2=3
    check("p7sdivp2", bv_lit(7, 4), bv_lit(2, 4), bv_lit(3, 4), true);
    check("n7sdivp2", bv_lit(9, 4), bv_lit(2, 4), bv_lit(13, 4), true);
    check("p7sdivn2", bv_lit(7, 4), bv_lit(14, 4), bv_lit(13, 4), true);
    check("n7sdivn2", bv_lit(9, 4), bv_lit(14, 4), bv_lit(3, 4), true);
    // round-toward-zero: -8/3 = -2 (NOT the floor -3)
    check("n8sdivp3", bv_lit(8, 4), bv_lit(3, 4), bv_lit(14, 4), true);
    // SDIV by zero = 0 (both signs)
    check("p5sdiv0", bv_lit(5, 4), bv_lit(0, 4), bv_lit(0, 4), true);
    check("n5sdiv0", bv_lit(11, 4), bv_lit(0, 4), bv_lit(0, 4), true);
    // INT_MIN / -1 = INT_MIN (overflow wraps, matching AArch64 SDIV)
    check("n8sdivn1", bv_lit(8, 4), bv_lit(15, 4), bv_lit(8, 4), true);
    // NEGATIVE control: 7/2 = 3, NOT 4 — a wrong quotient must be kernel-REJECTED.
    check(
        "p7sdivp2_wrong",
        bv_lit(7, 4),
        bv_lit(2, 4),
        bv_lit(4, 4),
        false,
    );
}

/// SHIFTS — differential validation (width 4) that bvShl/bvLShr/bvAShr compute the real
/// AArch64 shifts. Left shift truncates (5<<2 wraps to 4); LSR zero-fills (15>>1=7); ASR
/// sign-fills for negatives (-8>>1 = -4 = 12, -1>>1 = -1 = 15) and is LSR for non-negatives
/// (4>>1=2). Negative controls reject wrong results, incl. an ASR-vs-LSR control that pins
/// the sign-fill (ASR(-8,1)=12, NOT LSR's 4).
#[test]
fn test_bvshifts_are_faithful_real_shifts() {
    let mut env = env();
    let app2 = |nm: &str, a: Expr, b: Expr| Expr::apps(Expr::const_str(nm), [a, b]);
    let mut check = |label: &str, e: Expr, expected: Expr, should_pass: bool| {
        let ty = eq_list(e, expected.clone());
        let res = env.add_decl(crate::Declaration::Theorem {
            name: Name::from_string(&format!("Clean.BVC.__bvshift_diff_{label}")),
            level_params: vec![],
            type_: ty,
            value: eq_refl_list(expected),
        });
        assert_eq!(
            res.is_ok(),
            should_pass,
            "bvshift {label}: expected pass={should_pass}, got {res:?}"
        );
    };
    let shl = |a: Expr, b: Expr| app2(names::BV_SHL, a, b);
    let lshr = |a: Expr, b: Expr| app2(names::BV_LSHR, a, b);
    let ashr = |a: Expr, b: Expr| app2(names::BV_ASHR, a, b);
    // bvShl (logical left, truncating)
    check(
        "shl_1by1",
        shl(bv_lit(1, 4), bv_lit(1, 4)),
        bv_lit(2, 4),
        true,
    );
    check(
        "shl_3by2",
        shl(bv_lit(3, 4), bv_lit(2, 4)),
        bv_lit(12, 4),
        true,
    );
    check(
        "shl_5by2_wrap",
        shl(bv_lit(5, 4), bv_lit(2, 4)),
        bv_lit(4, 4),
        true,
    );
    check(
        "shl_7by0",
        shl(bv_lit(7, 4), bv_lit(0, 4)),
        bv_lit(7, 4),
        true,
    );
    // bvLShr (logical right, zero-fill)
    check(
        "lshr_8by1",
        lshr(bv_lit(8, 4), bv_lit(1, 4)),
        bv_lit(4, 4),
        true,
    );
    check(
        "lshr_15by1",
        lshr(bv_lit(15, 4), bv_lit(1, 4)),
        bv_lit(7, 4),
        true,
    );
    // bvAShr (arithmetic right): sign-fill for negatives, lshr for non-negatives
    check(
        "ashr_n8by1",
        ashr(bv_lit(8, 4), bv_lit(1, 4)),
        bv_lit(12, 4),
        true,
    );
    check(
        "ashr_n1by1",
        ashr(bv_lit(15, 4), bv_lit(1, 4)),
        bv_lit(15, 4),
        true,
    );
    check(
        "ashr_n8by3",
        ashr(bv_lit(8, 4), bv_lit(3, 4)),
        bv_lit(15, 4),
        true,
    );
    check(
        "ashr_p4by1",
        ashr(bv_lit(4, 4), bv_lit(1, 4)),
        bv_lit(2, 4),
        true,
    );
    // NEGATIVE controls
    check(
        "shl_wrong",
        shl(bv_lit(1, 4), bv_lit(1, 4)),
        bv_lit(3, 4),
        false,
    );
    check(
        "ashr_vs_lshr",
        ashr(bv_lit(8, 4), bv_lit(1, 4)),
        bv_lit(4, 4),
        false,
    );
}

/// COMPARES RUNG 1 — non-vacuity for the subtract-zero bridge `beq_eq_isZero_sub`.
/// The make-or-break: the kernel must REJECT a WRONG bridge that drops the `bvNot`
/// (i.e. claims `bvBeq a b = bvIsZero (addRecM a b true)` — ADD, not SUB). At a
/// discriminating concrete witness (a = [true], b = [true]: a==b is true, but
/// `addRecM [t] [t] true = [t] ` is non-zero so `bvIsZero` is false) the same
/// proof skeleton cannot retype, so the wrong statement is unprovable here.
#[test]
fn test_beq_is_zero_bridge_wrong_no_bvnot_is_rejected() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let mut env = env();
    let bt = Expr::const_str("Bool.true");
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    let beq = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::BV_BEQ), [x, y]);
    let isz = |x: Expr| Expr::app(Expr::const_str(names::BV_IS_ZERO), x);
    let addm =
        |a: Expr, b: Expr, c: Expr| Expr::apps(Expr::const_str("Clean.BVI.addRecM"), [a, b, c]);
    // WRONG bridge at the witness a=b=[true]: bvBeq [t] [t] = bvIsZero(addRecM [t] [t] true)
    // LHS reduces to `true`; RHS: addRecM [t] [t] true = [xor3 t t t] = [t], bvIsZero [t] = false.
    // So the claimed `true = false` is FALSE — `Eq.refl` of either side is ill-typed.
    let one = cons(bt.clone(), nil.clone());
    let wrong_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_str("Bool"),
            beq(one.clone(), one.clone()),
            isz(addm(one.clone(), one.clone(), bt.clone())),
        ],
    );
    let mut b = EnvDeclBuilder::new();
    // Attempt `Eq.refl true` (the bvBeq side) — must FAIL to typecheck against the wrong goal.
    let attempt = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), bt.clone()],
    );
    let _ = &mut b;
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.beq_bridge_WRONG_no_bvnot"),
        level_params: vec![],
        type_: wrong_ty,
        value: attempt,
    });
    assert!(
        res.is_err(),
        "the WRONG (no-bvNot/ADD) bridge must be KERNEL-REJECTED at a==b witness (true != false)"
    );
}

/// COMPARES RUNG 1 — non-vacuity for the branch-inversion identity `iteVal_not`.
/// The make-or-break: the kernel must REJECT the NON-inverted restatement
/// (`bvIteVal p u v` on the RHS instead of the swapped `bvIteVal p v u`), proving
/// `iteVal_not` is the genuine branch-swap and not a refl-closeable tautology.
#[test]
fn test_ite_val_not_is_genuine_branch_swap_mutation_rejected() {
    use crate::env::decl_builder::EnvDeclBuilder;
    let mut env = env();
    // Build the WRONG goal: ∀ p u v, bvIteVal (Bool.not p) u v = bvIteVal p u v
    // (RHS NOT swapped). At p=false: LHS ≡ u, RHS ≡ v — `Eq.refl u` does NOT
    // typecheck (u ≠ v in general), so the same proof term is REJECTED.
    let bool_ty = || Expr::const_str("Bool");
    let lb = list_bool();
    let bnot = |x: Expr| Expr::app(Expr::const_str("Bool.not"), x);
    let ite =
        |p: Expr, vt: Expr, ve: Expr| Expr::apps(Expr::const_str(names::BV_ITE_VAL), [p, vt, ve]);
    // wrong type
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(bool_ty());
    let (u_id, u) = b.fresh_local(lb.clone());
    let (v_id, v) = b.fresh_local(lb.clone());
    let wrong_goal = eq_list(
        ite(bnot(p.clone()), u.clone(), v.clone()),
        ite(p.clone(), u.clone(), v.clone()),
    ); // RHS NOT swapped
    let t = b.mk_pi(v_id, BinderInfo::Default, lb.clone(), wrong_goal);
    let t = b.mk_pi(u_id, BinderInfo::Default, lb.clone(), t);
    let wrong_ty = b.finish(b.mk_pi(p_id, BinderInfo::Default, bool_ty(), t));
    // Reuse the SAME proof shape iteVal_not uses (Bool.rec refl/refl). It proves
    // the CORRECT (swapped) goal; against the wrong goal it must fail to check.
    let mut b2 = EnvDeclBuilder::new();
    let (p2_id, p2) = b2.fresh_local(bool_ty());
    let (u2_id, u2) = b2.fresh_local(lb.clone());
    let (v2_id, v2) = b2.fresh_local(lb.clone());
    let motive = {
        let mut c = EnvDeclBuilder::child_of(&b2);
        let (x_id, x) = c.fresh_local(bool_ty());
        let body = eq_list(
            ite(bnot(x.clone()), u2.clone(), v2.clone()),
            ite(x.clone(), u2.clone(), v2.clone()),
        );
        c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_ty(), body))
    };
    let rec = Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [
            motive,
            eq_refl_list(u2.clone()),
            eq_refl_list(v2.clone()),
            p2.clone(),
        ],
    );
    let r = b2.mk_lam(v2_id, BinderInfo::Default, lb.clone(), rec);
    let r = b2.mk_lam(u2_id, BinderInfo::Default, lb.clone(), r);
    let wrong_val = b2.finish(b2.mk_lam(p2_id, BinderInfo::Default, bool_ty(), r));
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.iteVal_not_WRONG_noninverted"),
        level_params: vec![],
        type_: wrong_ty,
        value: wrong_val,
    });
    assert!(
        res.is_err(),
        "the NON-inverted iteVal_not restatement must be KERNEL-REJECTED (u != v at p=false); \
         if it type-checks, the branch-swap is vacuous"
    );
}

#[test]
fn test_extract_zeroext_identity_instantiates_at_width_32() {
    // The parametric identity at a width-32 list, padded by 32 (the gate's exact
    // Extract[31:0](ZeroExt_32(·)) shape): bvTakeLen z (bvZeroExt z 32) = z.
    let env = env();
    let z = bv_lit(0xDEAD_BEEF, 32);
    let thm = Expr::apps(
        Expr::const_str(names::EXTRACT_ZEXT_ID),
        [z.clone(), nat_lit(32)],
    );
    let expected = eq_list(take_len(z.clone(), zext(z.clone(), nat_lit(32))), z);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&thm, &expected)
        .expect("extract_zeroext_id instantiates at width 32");
}

#[test]
fn test_or_zero_identity_instantiates_at_width_32() {
    let env = env();
    let z = bv_lit(0x0123_4567, 32);
    let thm = Expr::app(Expr::const_str(names::OR_ZERO_ID), z.clone());
    let expected = eq_list(zip_or(all_false(z.clone()), z.clone()), z);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&thm, &expected)
        .expect("or_zero_id instantiates at width 32");
}

#[test]
fn test_identities_are_parametric_over_symbolic_z() {
    // POSITIVE (parametric, not ground): instantiate at a SYMBOLIC z : List Bool.
    // The proof must hold for ANY z (this is the whole point — the gate's BvAdd
    // subterm is symbolic from the identity's perspective).
    let mut env = env();
    env.add_decl(crate::Declaration::Axiom {
        name: Name::from_string("symz"),
        level_params: vec![],
        type_: list_bool(),
    })
    .expect("symz");
    let z = Expr::const_str("symz");
    let tc = TypeChecker::with_mode(&env, env.mode());
    // extract_zeroext_id symz 5 : bvTakeLen symz (bvZeroExt symz 5) = symz
    let thm1 = Expr::apps(
        Expr::const_str(names::EXTRACT_ZEXT_ID),
        [z.clone(), nat_lit(5)],
    );
    let exp1 = eq_list(take_len(z.clone(), zext(z.clone(), nat_lit(5))), z.clone());
    tc.check_type(&thm1, &exp1)
        .expect("extract_zeroext_id holds for SYMBOLIC z (parametric)");
    // or_zero_id symz : bvZipOr (bvAllFalse symz) symz = symz
    let thm2 = Expr::app(Expr::const_str(names::OR_ZERO_ID), z.clone());
    let exp2 = eq_list(zip_or(all_false(z.clone()), z.clone()), z);
    tc.check_type(&thm2, &exp2)
        .expect("or_zero_id holds for SYMBOLIC z (parametric)");
}

#[test]
fn test_symbolic_identity_goal_is_not_closeable_by_refl() {
    // NON-DEGENERACY (make-or-break): over a SYMBOLIC z, `bvTakeLen z (bvZeroExt
    // z k) = z` does NOT hold definitionally — the kernel cannot reduce
    // takeLen/zeroext without case-splitting z's spine. So a bare Eq.refl of the
    // LHS must be REJECTED; only the List.rec INDUCTION proof (extract_zeroext_id)
    // closes it. If a refl closed it, the identity would be a definitional triviality
    // and the inductive proof vacuous.
    let mut env = env();
    env.add_decl(crate::Declaration::Axiom {
        name: Name::from_string("symz_nd"),
        level_params: vec![],
        type_: list_bool(),
    })
    .expect("symz_nd");
    let z = Expr::const_str("symz_nd");
    let lhs = take_len(z.clone(), zext(z.clone(), nat_lit(3)));
    let goal = eq_list(lhs.clone(), z.clone());
    let refl_lhs = eq_refl_list(lhs);
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&refl_lhs, &goal).is_err(),
        "the SYMBOLIC extract∘zeroext identity must NOT close by Eq.refl — it requires \
         the List.rec induction; a refl-closure would make the inductive proof vacuous"
    );
    // Same for or_zero over symbolic z.
    let or_lhs = zip_or(all_false(z.clone()), z.clone());
    let or_goal = eq_list(or_lhs.clone(), z.clone());
    assert!(
        tc.check_type(&eq_refl_list(or_lhs), &or_goal).is_err(),
        "the SYMBOLIC or-zero identity must NOT close by Eq.refl"
    );
}

#[test]
fn test_mutant_zeroext_pads_true_breaks_identity() {
    // NON-VACUITY (mutant 1): if ZeroExt padded with TRUE instead of false, then
    // taking len(z) of (z ++ trues) still = z (the take only sees z's prefix)...
    // so THAT particular mutant does NOT break extract∘zeroext. The discriminating
    // mutant for extract∘zeroext is a WRONG TAKE LENGTH (see mutant 2/3). Here we
    // instead confirm the ZEROEXT op genuinely appends (not a stub returning z):
    // bvZeroExt [t] 1 must be [t,f] (length 2), NOT [t]. A refl claiming it equals
    // [t] (the stub behaviour) must be REJECTED.
    let env = env();
    let one = cons(btrue(), nil()); // [true], width 1
    let zexted = zext(one.clone(), nat_lit(1)); // should be [true, false]
    let tc = TypeChecker::with_mode(&env, env.mode());
    // FALSE claim: bvZeroExt [t] 1 = [t]  (would hold only if zext were a no-op stub)
    let bogus = eq_list(zexted.clone(), one.clone());
    let refl = eq_refl_list(one);
    assert!(
        tc.check_type(&refl, &bogus).is_err(),
        "bvZeroExt must genuinely append a pad bit; [t] zext 1 = [t] (stub) must be REJECTED"
    );
    // And the TRUE value: bvZeroExt [t] 1 = [t, f].
    let two = cons(btrue(), cons(bfalse(), nil()));
    tc.check_type(&eq_refl_list(two.clone()), &eq_list(zexted, two))
        .expect("bvZeroExt [t] 1 = [t,f] (real append of a false pad bit)");
}

#[test]
fn test_mutant_extract_wrong_offset_breaks_identity() {
    // NON-VACUITY (mutant 2): extract at the WRONG length. The identity needs
    // bvTakeLen z (...) where the take length is exactly len(z). If we take len
    // (z ++ [extra]) (one bit too many) of (z ++ pad), we get z ++ [first pad bit],
    // ≠ z. Concretely: z = [true] (len 1), zext by 1 → [true,false]. Taking length
    // of a length-2 list (e.g. [true,true]) of [true,false] yields [true,false] ≠
    // [true]. A refl claiming bvTakeLen [t,t] [t,f] = [t] must be REJECTED.
    let env = env();
    let len2 = cons(btrue(), cons(btrue(), nil())); // length-2 tag
    let src = cons(btrue(), cons(bfalse(), nil())); // [t,f]
    let wrong_take = take_len(len2, src.clone()); // = [t,f] (took 2), not [t]
    let one = cons(btrue(), nil());
    let tc = TypeChecker::with_mode(&env, env.mode());
    let bogus = eq_list(wrong_take.clone(), one);
    let refl = eq_refl_list(src); // [t,f]
                                  // refl of [t,f] against ([t,f] = [t]) — the RHS [t] differs, so REJECTED.
    assert!(
        tc.check_type(&refl, &bogus).is_err(),
        "taking the WRONG (too-long) length must not equal the original z; REJECTED"
    );
}

#[test]
fn test_mutant_or_nonzero_const_breaks_identity() {
    // NON-VACUITY (mutant 3): Or with a NONZERO const is NOT identity. zipOr [t] z
    // sets bit 0 regardless of z. At z = [false], zipOr [true] [false] = [true] ≠
    // [false]. A refl claiming zipOr [t] [f] = [f] must be REJECTED.
    let env = env();
    let one = cons(btrue(), nil()); // nonzero const [true]
    let zerobit = cons(bfalse(), nil()); // z = [false]
    let ored = zip_or(one, zerobit.clone()); // = [true]
    let tc = TypeChecker::with_mode(&env, env.mode());
    let bogus = eq_list(ored.clone(), zerobit.clone());
    let refl = eq_refl_list(cons(btrue(), nil())); // [true]
    assert!(
        tc.check_type(&refl, &bogus).is_err(),
        "zipOr with a NONZERO const must not be identity; zipOr [t] [f] = [f] REJECTED"
    );
    // And the real or-zero IS identity: zipOr [false] [false] = [false].
    let z = cons(bfalse(), nil());
    let af = all_false(z.clone());
    tc.check_type(&eq_refl_list(z.clone()), &eq_list(zip_or(af, z.clone()), z))
        .expect("zipOr (allFalse z) z = z holds (real or-zero identity)");
}

#[test]
fn test_bvf_lifted_identities_typecheck_at_a_concrete_embedding() {
    // The bvfEval-lifted identities at a concrete BvF: e = Leaf [t,f] (width 2).
    //   bvf_extract_zeroext_id (Leaf [t,f]) 2
    //     : bvfEval (ExtractLow (ZeroExt (Leaf [t,f]) 2) (Leaf [t,f])) = bvfEval (Leaf [t,f])
    //   bvf_or_zero_id (Leaf [t,f])
    //     : bvfEval (Or (Const (bvAllFalse (bvfEval (Leaf [t,f])))) (Leaf [t,f])) = bvfEval (Leaf [t,f])
    let env = env();
    let leaf = |l: Expr| Expr::app(Expr::const_str("Clean.BVC.BvF.Leaf"), l);
    let e = leaf(cons(btrue(), cons(bfalse(), nil())));
    let eval = |x: Expr| Expr::app(Expr::const_str(names::BVF_EVAL), x);
    let tc = TypeChecker::with_mode(&env, env.mode());

    // extract∘zeroext lifted
    let zext_f = Expr::apps(
        Expr::const_str("Clean.BVC.BvF.ZeroExt"),
        [e.clone(), nat_lit(2)],
    );
    let extract_f = Expr::apps(
        Expr::const_str("Clean.BVC.BvF.ExtractLow"),
        [zext_f, e.clone()],
    );
    let thm1 = Expr::apps(
        Expr::const_str(names::BVF_EXTRACT_ZEXT_ID),
        [e.clone(), nat_lit(2)],
    );
    let exp1 = eq_list(eval(extract_f), eval(e.clone()));
    tc.check_type(&thm1, &exp1)
        .expect("bvf_extract_zeroext_id typechecks at Leaf [t,f]");

    // or-zero lifted
    let const_f = Expr::app(
        Expr::const_str("Clean.BVC.BvF.Const"),
        all_false(eval(e.clone())),
    );
    let or_f = Expr::apps(Expr::const_str("Clean.BVC.BvF.Or"), [const_f, e.clone()]);
    let thm2 = Expr::app(Expr::const_str(names::BVF_OR_ZERO_ID), e.clone());
    let exp2 = eq_list(eval(or_f), eval(e));
    tc.check_type(&thm2, &exp2)
        .expect("bvf_or_zero_id typechecks at Leaf [t,f]");
}

// ── B2a: the COMPOSED gate-shape discharge (bvf_wrapper_id) ────────────────────

/// BvF constructor helpers for the gate-shape tests.
fn f_leaf(l: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.BvF.Leaf"), l)
}
fn f_const(l: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.BvF.Const"), l)
}
fn f_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.BvF.Add"), [a, b])
}
fn f_zext(e: Expr, k: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.BvF.ZeroExt"), [e, k])
}
fn f_extract(e: Expr, tag: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.BvF.ExtractLow"), [e, tag])
}
fn f_or(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.BvF.Or"), [a, b])
}
fn evalf(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BVF_EVAL), x)
}
/// The gate's move-via-ORR + W-register round-trip wrapper, at the BvF level:
/// `W(e,k) = ExtractLow( ZeroExt( Or(Const allFalse(eval e), e), k ), e )`.
fn f_wrap(e: Expr, k: Expr) -> Expr {
    f_extract(
        f_zext(f_or(f_const(all_false(evalf(e.clone()))), e.clone()), k),
        e,
    )
}

#[test]
fn test_wrapper_id_discharges_at_symbolic_inner() {
    // The COMPOSED discharge is parametric over the inner shared subterm: at a
    // SYMBOLIC BvF `e`, `bvfEval (W e k) = bvfEval e` typechecks. This is the
    // crux — the wrapper cancels regardless of what `e` denotes (in the gate it
    // is the BvAdd), and the proof is NOT a refl-collapse (the eval of the Or/
    // ZeroExt/Extract wrappers genuinely differs from eval e before the rewrite).
    let mut env = env();
    env.add_decl(crate::Declaration::Axiom {
        name: Name::from_string("syme"),
        level_params: vec![],
        type_: Expr::const_str(names::BVF),
    })
    .expect("syme");
    let e = Expr::const_str("syme");
    let thm = Expr::apps(
        Expr::const_str(names::BVF_WRAPPER_ID),
        [e.clone(), nat_lit(32)],
    );
    let expected = eq_list(evalf(f_wrap(e.clone(), nat_lit(32))), evalf(e));
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&thm, &expected)
        .expect("bvf_wrapper_id discharges the wrapper at a SYMBOLIC inner subterm (parametric)");
}

#[test]
fn test_composed_discharge_of_add_at_n_operand_wrappers() {
    // OPERAND-LEVEL congruence (NOT the full raw tree): discharge the add@N
    // OPERAND wrappers — `bvfEval(Add (W e0) (W e1)) = bvfEval(Add e0 e1)` — by
    // congruence over Add using `bvf_wrapper_id` at each operand. This checks the
    // OPERAND half of the gate's add@N shape; the OUTER result-level wrapper is NOT
    // assembled in this test — it is covered SEPARATELY by the PARAMETRIC
    // `bvf_wrapper_id` (checked at a symbolic inner in
    // `test_wrapper_id_discharges_at_symbolic_inner`). The FULL real-Formula
    // discharge (result + operand wrappers, over the gate's ACTUAL Formula) is the
    // trust-side B2b end-to-end test (ledger #38/#39), NOT this clean test.
    // Width-2 instance (e0=e1=Leaf[t,f]); the lemmas are parametric, so width is
    // immaterial to soundness.
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let e0 = f_leaf(cons(btrue(), cons(bfalse(), nil()))); // [t,f] = 1 @ w2
    let e1 = f_leaf(cons(bfalse(), cons(btrue(), nil()))); // [f,t] = 2 @ w2
    let n = nat_lit(2);

    // operand wrappers: W(e0), W(e1)
    let we0 = f_wrap(e0.clone(), n.clone());
    let we1 = f_wrap(e1.clone(), n.clone());
    // inner add over WRAPPED operands (as the raw tree has)
    let add_wrapped = f_add(we0.clone(), we1.clone());
    // auto add over BARE operands
    let auto = f_add(e0.clone(), e1.clone());

    // Goal we ultimately want for the operands: bvfEval add_wrapped = bvfEval auto.
    // Proof: congruence of Add over (W e0 = e0) and (W e1 = e1).
    // bvfEval(Add a b) = addRecM (bvfEval a) (bvfEval b) false — so we need
    // addRecM (eval (W e0)) (eval (W e1)) false = addRecM (eval e0) (eval e1) false,
    // via congrArg twice using bvf_wrapper_id e0 / e1.
    // We assemble it and check the type the KERNEL infers equals the operand-add goal.
    let wrap_e0 = Expr::apps(
        Expr::const_str(names::BVF_WRAPPER_ID),
        [e0.clone(), n.clone()],
    );
    let wrap_e1 = Expr::apps(
        Expr::const_str(names::BVF_WRAPPER_ID),
        [e1.clone(), n.clone()],
    );
    // addRecM applied: define a helper to build `addRecM x y false`.
    let add_rec_m = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_str(crate::bitvec_inductive::names::ADD_REC_M),
            [x, y, bfalse()],
        )
    };
    // congrArg (fun w => addRecM w (eval (W e1)) false) (wrap_e0 : eval(W e0)=eval e0)
    let l1 = Level::succ(Level::zero());
    let congr_ll = |a1: Expr, a2: Expr, f: Expr, h: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            [list_bool(), list_bool(), a1, a2, f, h],
        )
    };
    // step A: addRecM (eval (W e0)) (eval (W e1)) = addRecM (eval e0) (eval (W e1))
    let fa = {
        // fun w => addRecM w (eval (W e1)) false
        Expr::lam(
            BinderInfo::Default,
            list_bool(),
            add_rec_m(Expr::bvar(0), evalf(we1.clone())),
        )
    };
    let step_a = congr_ll(evalf(we0.clone()), evalf(e0.clone()), fa, wrap_e0);
    // step B: addRecM (eval e0) (eval (W e1)) = addRecM (eval e0) (eval e1)
    let fb = {
        Expr::lam(
            BinderInfo::Default,
            list_bool(),
            add_rec_m(evalf(e0.clone()), Expr::bvar(0)),
        )
    };
    let step_b = congr_ll(evalf(we1.clone()), evalf(e1.clone()), fb, wrap_e1);
    // chain A then B
    let eq_trans = |a: Expr, bm: Expr, c: Expr, h1: Expr, h2: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            [list_bool(), a, bm, c, h1, h2],
        )
    };
    let operand_proof = eq_trans(
        add_rec_m(evalf(we0), evalf(we1.clone())),
        add_rec_m(evalf(e0.clone()), evalf(we1)),
        add_rec_m(evalf(e0), evalf(e1)),
        step_a,
        step_b,
    );
    // expected: bvfEval (Add (W e0) (W e1)) = bvfEval (Add e0 e1)
    let operand_goal = eq_list(evalf(add_wrapped), evalf(auto));
    tc.check_type(&operand_proof, &operand_goal).expect(
        "composed discharge: the wrapped-operand add equals the bare-operand add \
         (gate add@N inner shape) via bvf_wrapper_id congruence",
    );
}

#[test]
fn test_wrong_op_at_discriminating_witness_is_rejected() {
    // A wrong op at a DISCRIMINATING WITNESS is kernel-REJECTED, confirming
    // `bvfEval` is NOT refl-degenerate (it genuinely distinguishes Add from Or).
    // NOTE (honesty): this exercises NEITHER bvf_wrapper_id NOR congrArg — it only
    // refutes a bare Eq.refl of a ground value mismatch (Add 1+1=2 vs Or 1|1=1). It
    // is NOT the composed-discharge negative control; the REAL composed-discharge
    // negative control (a corrupted machine_out reflects to a term whose discharge
    // fails the kernel) is the trust-side Trap-2 test b2b_reflected_corrupted_
    // machine_out_fails_discharge (ledger #38).
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let e0 = f_leaf(cons(btrue(), cons(bfalse(), nil())));
    let e1 = f_leaf(cons(bfalse(), cons(btrue(), nil())));
    // WRONG: Or instead of Add on the auto side.
    let bogus_auto = f_or(e0.clone(), e1.clone());
    let real_add = f_add(e0.clone(), e1.clone());
    // bvfEval(Add e0 e1) = addRecM ..; bvfEval(Or e0 e1) = bvZipOr .. — different.
    // A refl claiming they are equal must be REJECTED (Add 1+2=3 vs Or 1|2=3... at
    // [t,f]|[f,t] = [t,t] = 3, and Add [t,f]+[f,t] = [t,t] = 3 — coincide at THIS
    // input! choose inputs where they differ: e0=e1=[t,f] (1): Add=2=[f,t], Or=1=[t,f]).
    let s0 = f_leaf(cons(btrue(), cons(bfalse(), nil()))); // 1
    let add_s = f_add(s0.clone(), s0.clone()); // 1+1 = 2 = [f,t]
    let or_s = f_or(s0.clone(), s0.clone()); // 1|1 = 1 = [t,f]
    let bogus_goal = eq_list(evalf(add_s.clone()), evalf(or_s));
    let refl = eq_refl_list(evalf(add_s));
    assert!(
        tc.check_type(&refl, &bogus_goal).is_err(),
        "Add (1+1=2) must NOT be provably equal to Or (1|1=1); a wrong-op discharge \
         is REJECTED (no false grade)"
    );
    // (and the structurally-distinct bogus_auto vs real_add are different terms)
    let _ = (bogus_auto, real_add);
}

#[test]
fn test_bvult_computes_real_unsigned_lt() {
    // GENUINELY-COMPUTING check: bvUlt [false,true] [true,false] (LSB-first: 2 vs 1)
    // should be FALSE (2 < 1 is false); bvUlt [true,false] [false,true] (1 vs 2) TRUE.
    let env = env();
    let tc = crate::TypeChecker::with_mode(&env, env.mode());
    let bt = Expr::const_str("Bool.true");
    let bf = Expr::const_str("Bool.false");
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    let lst = |bits: &[bool]| {
        let mut acc = nil.clone();
        for &b in bits.iter().rev() {
            acc = cons(if b { bt.clone() } else { bf.clone() }, acc);
        }
        acc
    };
    let ult = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_ULT), [a, b]);
    let eqb = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), x, y],
        )
    };
    let refl = |v: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), v],
        )
    };
    // 2 = [false,true] (bit0=0,bit1=1); 1 = [true,false]
    let two = lst(&[false, true]);
    let one = lst(&[true, false]);
    // bvUlt 2 1 = false
    assert!(
        tc.check_type(
            &refl(bf.clone()),
            &eqb(ult(two.clone(), one.clone()), bf.clone())
        )
        .is_ok(),
        "bvUlt 2 1 must reduce to false"
    );
    // bvUlt 1 2 = true
    assert!(
        tc.check_type(&refl(bt.clone()), &eqb(ult(one, two), bt.clone()))
            .is_ok(),
        "bvUlt 1 2 must reduce to true"
    );
}

#[test]
fn test_bvsltreal_computes_real_signed_lt() {
    // FAITHFULNESS check: bvSLtReal on 3-bit signed values.
    //  [true,true,true] = -1 (LSB-first: 1+2+4=7 unsigned, MSB set -> -1 signed)
    //  [false,false,false] = 0 ;  [true,false,true]=5u=-3s ; [false,true,false]=2
    let env = env();
    let tc = crate::TypeChecker::with_mode(&env, env.mode());
    let bt = Expr::const_str("Bool.true");
    let bf = Expr::const_str("Bool.false");
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    let lst = |bits: &[bool]| {
        let mut acc = nil.clone();
        for &b in bits.iter().rev() {
            acc = cons(if b { bt.clone() } else { bf.clone() }, acc);
        }
        acc
    };
    let slt = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_SLT_REAL), [a, b]);
    let eqb = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), x, y],
        )
    };
    let refl = |v: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), v],
        )
    };
    let neg1 = lst(&[true, true, true]); // -1
    let zero = lst(&[false, false, false]); // 0
    let neg3 = lst(&[true, false, true]); // 5u = -3s
    let two = lst(&[false, true, false]); // 2
                                          // -1 <s 0  -> true
    assert!(
        tc.check_type(
            &refl(bt.clone()),
            &eqb(slt(neg1.clone(), zero.clone()), bt.clone())
        )
        .is_ok(),
        "-1 <s 0 must be true"
    );
    // 0 <s -1  -> false
    assert!(
        tc.check_type(
            &refl(bf.clone()),
            &eqb(slt(zero.clone(), neg1.clone()), bf.clone())
        )
        .is_ok(),
        "0 <s -1 must be false"
    );
    // -3 <s 2 -> true
    assert!(
        tc.check_type(&refl(bt.clone()), &eqb(slt(neg3, two.clone()), bt.clone()))
            .is_ok(),
        "-3 <s 2 must be true"
    );
    // 2 <s 0 -> false
    assert!(
        tc.check_type(&refl(bf.clone()), &eqb(slt(two, zero), bf.clone()))
            .is_ok(),
        "2 <s 0 must be false"
    );
}

/// COMPARES RUNG (slt) — non-vacuity / wrong-flag-rejection for `slt_flag_bridge`.
/// The bridge proves `bvSLtReal a b = Bool.xor N V` (N = sign of a−b, V = signed
/// overflow). The make-or-break: a WRONG bridge that DROPS the overflow XOR and
/// claims `bvSLtReal a b = N` must be KERNEL-REJECTED. Discriminating witness
/// (width 2, LSB-first): a = 0 = [false,false], b = −2 = [false,true].
///   bvSLtReal a b = (0 <s −2) = FALSE, but N (MSB of a−b = [false,false]−[false,true])
///   = TRUE. So `bvSLtReal a b = N` claims `false = true` — unprovable here.
/// The CORRECT N⊕V = false ⇒ the genuine bridge instance holds (sanity arm).
#[test]
fn test_slt_bridge_wrong_drops_overflow_xor_is_rejected() {
    let mut env = env();
    let bt = Expr::const_str("Bool.true");
    let bf = Expr::const_str("Bool.false");
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    let lst = |bits: &[bool]| {
        let mut acc = nil.clone();
        for &b in bits.iter().rev() {
            acc = cons(if b { bt.clone() } else { bf.clone() }, acc);
        }
        acc
    };
    let slt = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_SLT_REAL), [a, b]);
    let lastbit = |x: Expr| Expr::app(Expr::const_str(names::BV_LAST_BIT), x);
    let bvnot = |x: Expr| Expr::app(Expr::const_str("Clean.BVC.bvNot"), x);
    let addm =
        |a: Expr, b: Expr, c: Expr| Expr::apps(Expr::const_str("Clean.BVI.addRecM"), [a, b, c]);
    let eqb = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), x, y],
        )
    };
    let refl = |v: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), v],
        )
    };
    // a = 0 = [false,false] ; b = -2 = [false,true]  (LSB-first, width 2)
    let a = lst(&[false, false]);
    let b = lst(&[false, true]);
    // N = bvLastBit (addRecM a (bvNot b) true)
    let n_flag = lastbit(addm(a.clone(), bvnot(b.clone()), bt.clone()));
    // WRONG bridge instance: bvSLtReal a b = N  (drops the V XOR). LHS=false, N=true.
    let wrong_ty = eqb(slt(a.clone(), b.clone()), n_flag.clone());
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.slt_bridge_WRONG_drops_V"),
        level_params: vec![],
        type_: wrong_ty,
        value: refl(bf.clone()), // try the bvSLtReal side (false)
    });
    assert!(res.is_err(), "WRONG slt bridge (= N, no overflow XOR) must be kernel-REJECTED at the 0 vs -2 witness (false != true)");
    // sanity: the TRUE value bvSLtReal a b = false reduces by refl (faithfulness).
    let tc = crate::TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&refl(bf.clone()), &eqb(slt(a, b), bf))
            .is_ok(),
        "bvSLtReal 0 (-2) must reduce to false"
    );
}

/// NON-VACUITY for the conditional-discharge keystone `divGuardBridge`. The lemma
/// `bvIsZero b = false → bvIteVal (bvIsZero b) z dv = dv` GENUINELY USES the
/// precondition. Two mutations must be KERNEL-REJECTED:
///  (1) DROP the hypothesis: the UNCONDITIONAL `∀ b z dv, bvIteVal (bvIsZero b) z dv = dv`
///      is FALSE at b=[false] (bvIsZero=true ⇒ picks the THEN branch z, not dv) — the
///      proof skeleton (which needs the hypothesis to rewrite the guard) cannot retype.
///  (2) WRONG guard polarity at a discriminating concrete witness: at b=[false] the
///      claim `bvIteVal (bvIsZero [false]) z dv = dv` is `z = dv`, refl-unprovable for z≠dv.
#[test]
fn test_div_guard_bridge_dropping_precondition_is_rejected() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let mut env = env();
    let lb = || {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_str("Bool"),
        )
    };
    let bf = Expr::const_str("Bool.false");
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    let iz = |x: Expr| Expr::app(Expr::const_str(names::BV_IS_ZERO), x);
    let ite =
        |p: Expr, z: Expr, dv: Expr| Expr::apps(Expr::const_str(names::BV_ITE_VAL), [p, z, dv]);
    let eql = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [lb(), x, y],
        )
    };
    let refll = |x: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [lb(), x],
        )
    };

    // MUTATION (1): the UNCONDITIONAL lemma type ∀ b z dv, bvIteVal (bvIsZero b) z dv = dv,
    // proved by the keystone's would-be base `Eq.refl dv` (no hypothesis to rewrite the guard).
    let uncond_ty = {
        let mut b = EnvDeclBuilder::new();
        let (bb_id, bb) = b.fresh_local(lb());
        let (z_id, z) = b.fresh_local(lb());
        let (dv_id, dv) = b.fresh_local(lb());
        let g = eql(ite(iz(bb.clone()), z.clone(), dv.clone()), dv.clone());
        let t = b.mk_pi(dv_id, BinderInfo::Default, lb(), g);
        let t = b.mk_pi(z_id, BinderInfo::Default, lb(), t);
        b.finish(b.mk_pi(bb_id, BinderInfo::Default, lb(), t))
    };
    let uncond_val = {
        let mut b = EnvDeclBuilder::new();
        let (bb_id, _bb) = b.fresh_local(lb());
        let (z_id, _z) = b.fresh_local(lb());
        let (dv_id, dv) = b.fresh_local(lb());
        // `Eq.refl dv` : bvIteVal (bvIsZero b) z dv = dv  — would need the guard to reduce to false,
        // which it does NOT for symbolic b (no hypothesis). Kernel must REJECT.
        let r = b.mk_lam(dv_id, BinderInfo::Default, lb(), refll(dv.clone()));
        let r = b.mk_lam(z_id, BinderInfo::Default, lb(), r);
        b.finish(b.mk_lam(bb_id, BinderInfo::Default, lb(), r))
    };
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.divGuardBridge_WRONG_unconditional"),
        level_params: vec![],
        type_: uncond_ty,
        value: uncond_val,
    });
    assert!(
        res.is_err(),
        "the UNCONDITIONAL guard lemma (precondition dropped) must be KERNEL-REJECTED"
    );

    // MUTATION (2): concrete discriminating witness b=[false] (bvIsZero=true → THEN branch z).
    // Claim `bvIteVal (bvIsZero [false]) z dv = dv` ≡ `z = dv`; with z=[true], dv=[false] it is
    // `[true] = [false]`, and `Eq.refl dv` does NOT typecheck.
    let zero1 = cons(bf.clone(), nil.clone()); // b = [false]
    let z_t = cons(Expr::const_str("Bool.true"), nil.clone()); // z = [true]
    let dv_f = cons(bf.clone(), nil.clone()); // dv = [false]
    let wrong_ty = eql(
        ite(iz(zero1.clone()), z_t.clone(), dv_f.clone()),
        dv_f.clone(),
    );
    let tc = crate::TypeChecker::with_mode(&env, env.mode());
    assert!(tc.check_type(&refll(dv_f.clone()), &wrong_ty).is_err(),
        "guard at b=[false] picks z=[true]≠dv=[false]; the unconditional claim must be kernel-REJECTED");
}

/// NON-VACUITY for selectStoreDiff: the `bvBeq a a' = false` hypothesis is LOAD-BEARING. The
/// UNCONDITIONAL variant (hypothesis dropped) is KERNEL-REJECTED — at a'=a a load reads the STORED
/// `v`, not `bvSelect m a`, so `bvSelect (bvStore m a v) a'` is NOT defeq `bvSelect m a'` (the guard
/// bvBeq a a' is stuck for symbolic a,a'), and `Eq.refl (bvSelect m a')` cannot prove it.
#[test]
fn test_select_store_diff_dropping_hypothesis_is_rejected() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let mut env = env();
    let lb = || {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_str("Bool"),
        )
    };
    let arr = || Expr::arrow(lb(), lb());
    let sel = |m: Expr, a: Expr| Expr::apps(Expr::const_str(names::BV_SELECT), [m, a]);
    let sto = |m: Expr, a: Expr, v: Expr| Expr::apps(Expr::const_str(names::BV_STORE), [m, a, v]);
    let eql = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [lb(), x, y],
        )
    };
    let refll = |x: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [lb(), x],
        )
    };
    // UNCONDITIONAL: ∀ m a a' v, bvSelect (bvStore m a v) a' = bvSelect m a'  (hypothesis DROPPED).
    let uncond_ty = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(arr());
        let (a_id, a) = b.fresh_local(lb());
        let (ap_id, ap) = b.fresh_local(lb());
        let (v_id, v) = b.fresh_local(lb());
        let g = eql(
            sel(sto(m.clone(), a.clone(), v.clone()), ap.clone()),
            sel(m.clone(), ap.clone()),
        );
        let t = b.mk_pi(v_id, BinderInfo::Default, lb(), g);
        let t = b.mk_pi(ap_id, BinderInfo::Default, lb(), t);
        let t = b.mk_pi(a_id, BinderInfo::Default, lb(), t);
        b.finish(b.mk_pi(m_id, BinderInfo::Default, arr(), t))
    };
    let uncond_val = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(arr());
        let (a_id, _a) = b.fresh_local(lb());
        let (ap_id, ap) = b.fresh_local(lb());
        let (v_id, _v) = b.fresh_local(lb());
        let r = b.mk_lam(
            v_id,
            BinderInfo::Default,
            lb(),
            refll(sel(m.clone(), ap.clone())),
        );
        let r = b.mk_lam(ap_id, BinderInfo::Default, lb(), r);
        let r = b.mk_lam(a_id, BinderInfo::Default, lb(), r);
        b.finish(b.mk_lam(m_id, BinderInfo::Default, arr(), r))
    };
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.selectStoreDiff_WRONG_unconditional"),
        level_params: vec![],
        type_: uncond_ty,
        value: uncond_val,
    });
    assert!(
        res.is_err(),
        "the UNCONDITIONAL selectStoreDiff (hypothesis dropped) must be KERNEL-REJECTED"
    );
}

/// NON-VACUITY for bvBeqConsFalse: the `Bool.xor h1 h2 = true` hypothesis is LOAD-BEARING.
/// The UNCONDITIONAL variant `∀ h1 h2 t1 t2, bvBeq (h1::t1) (h2::t2) = false` is FALSE (take
/// h1=h2, t1=t2 ⇒ bvBeq = true ≠ false) and must be KERNEL-REJECTED: for symbolic heads
/// `Bool.xor h1 h2` is STUCK, so `bvBeq (h1::t1) (h2::t2)` does NOT reduce to `false` and
/// `Eq.refl false` cannot prove it.
#[test]
fn test_bv_beq_cons_false_dropping_hypothesis_is_rejected() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let mut env = env();
    let boolt = || Expr::const_str("Bool");
    let lb = || {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_str("Bool"),
        )
    };
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let beq = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::BV_BEQ), [x, y]);
    let eqb = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [boolt(), x, y],
        )
    };
    let reflb = |x: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [boolt(), x],
        )
    };
    // UNCONDITIONAL: ∀ h1 h2 t1 t2, bvBeq (h1::t1) (h2::t2) = false  (hypothesis DROPPED).
    let uncond_ty = {
        let mut b = EnvDeclBuilder::new();
        let (h1_id, h1) = b.fresh_local(boolt());
        let (h2_id, h2) = b.fresh_local(boolt());
        let (t1_id, t1) = b.fresh_local(lb());
        let (t2_id, t2) = b.fresh_local(lb());
        let g = eqb(
            beq(cons(h1.clone(), t1.clone()), cons(h2.clone(), t2.clone())),
            Expr::const_str("Bool.false"),
        );
        let t = b.mk_pi(t2_id, BinderInfo::Default, lb(), g);
        let t = b.mk_pi(t1_id, BinderInfo::Default, lb(), t);
        let t = b.mk_pi(h2_id, BinderInfo::Default, boolt(), t);
        b.finish(b.mk_pi(h1_id, BinderInfo::Default, boolt(), t))
    };
    let uncond_val = {
        let mut b = EnvDeclBuilder::new();
        let (h1_id, _h1) = b.fresh_local(boolt());
        let (h2_id, _h2) = b.fresh_local(boolt());
        let (t1_id, _t1) = b.fresh_local(lb());
        let (t2_id, _t2) = b.fresh_local(lb());
        let r = b.mk_lam(
            t2_id,
            BinderInfo::Default,
            lb(),
            reflb(Expr::const_str("Bool.false")),
        );
        let r = b.mk_lam(t1_id, BinderInfo::Default, lb(), r);
        let r = b.mk_lam(h2_id, BinderInfo::Default, boolt(), r);
        b.finish(b.mk_lam(h1_id, BinderInfo::Default, boolt(), r))
    };
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.bvBeqConsFalse_WRONG_unconditional"),
        level_params: vec![],
        type_: uncond_ty,
        value: uncond_val,
    });
    assert!(
        res.is_err(),
        "the UNCONDITIONAL bvBeqConsFalse (xor-hypothesis dropped) must be KERNEL-REJECTED"
    );
}

/// NON-VACUITY for bvTakeLenApkend: the PREFIX structure (take-tag `s` == the appended
/// prefix) is LOAD-BEARING. Decoupling them — `∀ s a w, bvTakeLen s (bvAppend a w) = s`
/// with `a` independent of `s` — is FALSE (take a=nil, w=nil, s=[true] ⇒ bvTakeLen [t] nil
/// = nil ≠ [t]) and must be KERNEL-REJECTED: for symbolic s,a `bvTakeLen s (bvAppend a w)`
/// does not reduce to `s`, so `Eq.refl s` cannot prove it.
#[test]
fn test_bv_take_len_append_dropping_prefix_structure_is_rejected() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::expr::BinderInfo;
    let mut env = env();
    let lb = || {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_str("Bool"),
        )
    };
    let take_len = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::TAKE_LEN), [x, y]);
    let append = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::APPEND), [x, y]);
    let eql = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [lb(), x, y],
        )
    };
    let refll = |x: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [lb(), x],
        )
    };
    // WRONG: ∀ s a w, bvTakeLen s (bvAppend a w) = s  (prefix `a` DECOUPLED from tag `s`).
    let wrong_ty = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(lb());
        let (a_id, a) = b.fresh_local(lb());
        let (w_id, w) = b.fresh_local(lb());
        let g = eql(take_len(s.clone(), append(a.clone(), w.clone())), s.clone());
        let t = b.mk_pi(w_id, BinderInfo::Default, lb(), g);
        let t = b.mk_pi(a_id, BinderInfo::Default, lb(), t);
        b.finish(b.mk_pi(s_id, BinderInfo::Default, lb(), t))
    };
    let wrong_val = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(lb());
        let (a_id, _a) = b.fresh_local(lb());
        let (w_id, _w) = b.fresh_local(lb());
        let r = b.mk_lam(w_id, BinderInfo::Default, lb(), refll(s.clone()));
        let r = b.mk_lam(a_id, BinderInfo::Default, lb(), r);
        b.finish(b.mk_lam(s_id, BinderInfo::Default, lb(), r))
    };
    let res = env.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BVC.bvTakeLenAppend_WRONG_decoupled"),
        level_params: vec![],
        type_: wrong_ty,
        value: wrong_val,
    });
    assert!(
        res.is_err(),
        "the DECOUPLED bvTakeLenAppend (prefix != tag) must be KERNEL-REJECTED"
    );
}

/// NON-VACUITY for the memory keystone `selectStoreSame` (read-over-write). The
/// lemma GENUINELY USES the store at the SAME address. Two mutations must be
/// KERNEL-REJECTED at a discriminating witness:
///  (1) WRONG-ADDRESS read: bvSelect (bvStore m a v) a'  with a'≠a reads `m a'`
///      (the unmodified cell), NOT v. At a=[true], a'=[false], v=[true], m=λ_.[false]:
///      Select(Store(m,[t],[t]),[f]) = bvIteVal (bvBeq [t] [f]) [t] (m [f])
///        = bvIteVal false [t] [f] = [f] ≠ [t]=v.
///  (2) NO-STORE: bvSelect m a = v for an arbitrary m is false (m a need not be v).
#[test]
fn test_select_store_same_wrong_address_is_rejected() {
    let env = env();
    let bt = Expr::const_str("Bool.true");
    let bf = Expr::const_str("Bool.false");
    let lb = || {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_str("Bool"),
        )
    };
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    let sel = |m: Expr, a: Expr| Expr::apps(Expr::const_str(names::BV_SELECT), [m, a]);
    let sto = |m: Expr, a: Expr, v: Expr| Expr::apps(Expr::const_str(names::BV_STORE), [m, a, v]);
    let eql = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [lb(), x, y],
        )
    };
    let refll = |x: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [lb(), x],
        )
    };
    let tc = crate::TypeChecker::with_mode(&env, env.mode());
    // const array m = λ _ => [false]
    let const_f = {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;
        let mut b = EnvDeclBuilder::new();
        let (w_id, _w) = b.fresh_local(lb());
        b.finish(b.mk_lam(
            w_id,
            BinderInfo::Default,
            lb(),
            cons(bf.clone(), nil.clone()),
        ))
    };
    let a_t = cons(bt.clone(), nil.clone()); // a = [true]
    let a_f = cons(bf.clone(), nil.clone()); // a' = [false]
    let v_t = cons(bt.clone(), nil.clone()); // v = [true]
                                             // MUTATION (1): wrong-address read claims = v ([true]); actually reads m a' = [false].
    let wrong_ty = eql(
        sel(sto(const_f.clone(), a_t.clone(), v_t.clone()), a_f.clone()),
        v_t.clone(),
    );
    assert!(tc.check_type(&refll(v_t.clone()), &wrong_ty).is_err(),
        "wrong-address read (a'=[false]≠a=[true]) returns m a'=[false]≠v=[true]; must be kernel-REJECTED");
    // POSITIVE arm: the SAME-address read DOES return v (the keystone holds concretely).
    let right_ty = eql(
        sel(sto(const_f.clone(), a_t.clone(), v_t.clone()), a_t.clone()),
        v_t.clone(),
    );
    assert!(
        tc.check_type(&refll(v_t.clone()), &right_ty).is_ok(),
        "same-address read must return v (selectStoreSame holds at the witness)"
    );
    // MUTATION (2): no-store — Select(m, a) = v is false (m a = [false] ≠ [true]).
    let nostore_ty = eql(sel(const_f.clone(), a_t.clone()), v_t.clone());
    assert!(
        tc.check_type(&refll(v_t.clone()), &nostore_ty).is_err(),
        "no-store read Select(m,a) returns m a=[false]≠v=[true]; must be kernel-REJECTED"
    );
}

#[test]
fn test_bvmul_computes_real_multiply() {
    // FAITHFULNESS: bvMul on small LSB-first vectors equals integer multiply (mod 2^w).
    // Differential vs a Rust reference multiplier over a sweep of widths/values; the
    // kernel checks each product by Eq.refl (bvMul reduces to the literal product list).
    let env = env();
    let tc = crate::TypeChecker::with_mode(&env, env.mode());
    let bt = Expr::const_str("Bool.true");
    let bf = Expr::const_str("Bool.false");
    let cons = |h: Expr, t: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [Expr::const_str("Bool"), h, t],
        )
    };
    let nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        [Expr::const_str("Bool")],
    );
    // LSB-first width-w literal
    let lit = |val: u64, w: u32| {
        let mut acc = nil.clone();
        for k in (0..w).rev() {
            acc = cons(
                if (val >> k) & 1 == 1 {
                    bt.clone()
                } else {
                    bf.clone()
                },
                acc,
            );
        }
        acc
    };
    let mul = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BV_MUL), [a, b]);
    let eql = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [list_bool(), x, y],
        )
    };
    let refl = |x: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [list_bool(), x],
        )
    };
    // bvMul result width = width of operand a (the recursion var); product taken mod 2^w_a,
    // but the shift-add grows; we compare against the value bvMul actually produces by
    // checking bvMul a b == lit(expected, len) where len is bvMul's natural output length.
    // To keep the check refl-clean, verify the LOW w_a bits match (a*b mod 2^w_a) — the
    // discharge only needs the same function on both sides, but faithfulness wants the
    // genuine product. We verify low-bits equality at several samples.
    let cases: &[(u64, u64, u32)] = &[
        (0, 0, 4),
        (1, 1, 4),
        (2, 3, 4),
        (3, 3, 4),
        (5, 5, 4),
        (7, 2, 4),
        (6, 7, 4),
        (1, 13, 4),
        (11, 9, 5),
        (21, 17, 6),
        (3, 100, 8),
        (255, 2, 8),
    ];
    let mut ok = 0usize;
    for &(a, b, w) in cases {
        let prod = a.wrapping_mul(b) & ((1u64 << w) - 1);
        // bvMul (lit a w)(lit b w) — its output, truncated to low w bits via bvTakeLen, equals lit(prod, w).
        let take_len =
            |tag: Expr, xs: Expr| Expr::apps(Expr::const_str(names::TAKE_LEN), [tag, xs]);
        let lhs = take_len(lit(0, w), mul(lit(a, w), lit(b, w)));
        let goal = eql(lhs.clone(), lit(prod, w));
        if tc.check_type(&refl(lit(prod, w)), &goal).is_ok() {
            ok += 1;
        } else {
            panic!("bvMul faithfulness FAILED at {a}*{b} mod 2^{w} = {prod}");
        }
    }
    assert_eq!(
        ok,
        cases.len(),
        "all bvMul differential samples must match integer multiply (mod 2^w)"
    );
}
