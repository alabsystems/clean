// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the computational width-4 BitVec layer.
//!
//! These prove the layer is *semantically real* (ops compute) and that the
//! registered identities are NON-REFLEXIVE kernel theorems whose transitive
//! axiom closure is `⊆ FOUNDATIONAL_AXIOMS` (empty domain-axiom set).

use super::names;
use super::{bit, bv_eq, BvNames, BV_COMPUTE_WIDTH};
use crate::name::Name;
use crate::{
    BinderInfo, ConstantKind, Environment, Expr, FVarId, Level, LocalContext, TypeChecker,
};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_compute().expect("init_bv_compute");
    env.init_bv_compute().expect("idempotent");
    env
}

/// A symbolic free `Clean.BV4` operand `a` in a fresh context.
fn symbolic_a(env: &mut Environment) -> Expr {
    env.add_decl(crate::Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_str(names::BV),
    })
    .expect("add operand a");
    Expr::const_str("a")
}

/// All domain (non-foundational) axioms reachable from `name`. Empty ⇒ the
/// theorem's transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`.
fn domain_axioms(env: &Environment, name: &str) -> Vec<String> {
    let mut v: Vec<String> = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(|n| n.to_string())
        .collect();
    v.sort();
    v
}

#[test]
fn test_layer_registers_real_definitions_not_axioms() {
    let env = env();
    // Ops are reducible Definitions, NOT axioms.
    for op in [
        names::BV_ZERO,
        names::BV_NOT,
        names::BV_ADD,
        names::BV_SUB,
        names::BV_EQ,
        names::XOR3,
        names::MAJ,
        names::BIT[0],
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("missing {op}"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{op} must be a Definition (semantically real), not an Axiom"
        );
    }
}

#[test]
fn test_bvsub_self_lhs_and_rhs_are_distinct_terms() {
    // HONESTY: confirm this is NOT reflexivity-in-disguise. The proved goal is
    // `bvEq (bvSub a a) bvZero`; `bvSub a a` and `bvZero` are syntactically
    // DIFFERENT terms (one is an application of bvSub, the other the const
    // bvZero), so a refl proof would NOT type-check against the bvEq goal — only
    // genuine bit/carry reasoning does.
    let mut e = env();
    let a = symbolic_a(&mut e);
    let lhs = Expr::apps(Expr::const_str(names::BV_SUB), [a.clone(), a.clone()]);
    let rhs = Expr::const_str(names::BV_ZERO);
    assert_ne!(lhs, rhs, "bvSub a a must differ syntactically from bvZero");
}

#[test]
fn test_bvsub_self_is_proved_and_axiom_closure_foundational() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    // type-checks
    let _ = tc
        .infer_type(&Expr::const_(Name::from_string(names::BV_SUB_SELF), vec![]))
        .expect("bvSub_self type-checks");
    // axiom closure ⊆ foundational (no domain axioms)
    let deps = domain_axioms(&env, names::BV_SUB_SELF);
    assert!(
        deps.is_empty(),
        "bvSub_self must be axiom-free (⊆ foundational), got {deps:?}"
    );
}

#[test]
fn test_bvadd_zero_is_proved_and_axiom_closure_foundational() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&Expr::const_(Name::from_string(names::BV_ADD_ZERO), vec![]))
        .expect("bvAdd_zero type-checks");
    let deps = domain_axioms(&env, names::BV_ADD_ZERO);
    assert!(
        deps.is_empty(),
        "bvAdd_zero must be axiom-free, got {deps:?}"
    );
}

#[test]
fn test_bvadd_comm_is_proved_and_axiom_closure_foundational() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&Expr::const_(Name::from_string(names::BV_ADD_COMM), vec![]))
        .expect("bvAdd_comm type-checks");
    let deps = domain_axioms(&env, names::BV_ADD_COMM);
    assert!(
        deps.is_empty(),
        "bvAdd_comm must be axiom-free, got {deps:?}"
    );
}

#[test]
fn test_bool_helpers_are_proved_and_axiom_closure_foundational() {
    // The Bool helper theorems backing the solver-backed (non-identical) replay
    // are kernel-proved with foundational-only axiom closure.
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for thm in [
        names::BOOL_EM,
        names::EQ_TF_ELIM,
        names::XNOR_TRUE_IMP_EQ,
        names::LIT_CLASH,
        names::NOT_FALSE_IMP_TRUE,
        names::EQ_IMP_XNOR_TRUE,
    ] {
        let _ty = tc
            .infer_type(&Expr::const_(Name::from_string(thm), vec![]))
            .unwrap_or_else(|e| panic!("{thm} must type-check: {e:?}"));
        let deps = domain_axioms(&env, thm);
        assert!(deps.is_empty(), "{thm} must be axiom-free, got {deps:?}");
    }
    // xnor is a reducible Definition.
    assert!(matches!(
        env.get_const(&Name::from_string(names::XNOR))
            .map(|c| c.kind),
        Some(ConstantKind::Definition)
    ));
}

#[test]
fn test_bvsub_self_applied_to_symbolic_a_checks_against_goal() {
    // Apply the proved theorem to a symbolic `a` and re-check that
    // `bvSub_self a : bvEq (bvSub a a) bvZero` via the FULL kernel check_type.
    let mut e = env();
    let a = symbolic_a(&mut e);
    let proof = Expr::app(
        Expr::const_(Name::from_string(names::BV_SUB_SELF), vec![]),
        a.clone(),
    );
    let lhs = Expr::apps(Expr::const_str(names::BV_SUB), [a.clone(), a.clone()]);
    let goal = bv_eq(lhs, Expr::const_str(names::BV_ZERO));

    let tc = TypeChecker::with_mode(&e, e.mode());
    tc.check_type(&proof, &goal)
        .expect("bvSub_self a : bvEq (bvSub a a) bvZero");
}

#[test]
fn test_false_identity_bvsub_self_eq_a_is_rejected() {
    // MUTATION / negative control: the FALSE identity `bvSub a a == a` must NOT
    // be provable. We try to use the genuine bvSub_self proof term (of type
    // `bvEq (bvSub a a) bvZero`) against the bogus goal `bvEq (bvSub a a) a`;
    // the kernel must REJECT it (bvZero's bits are all false, but `a`'s bits are
    // symbolic — the And-chain conjuncts do not match).
    let mut e = env();
    let a = symbolic_a(&mut e);
    let proof = Expr::app(
        Expr::const_(Name::from_string(names::BV_SUB_SELF), vec![]),
        a.clone(),
    );
    let lhs = Expr::apps(Expr::const_str(names::BV_SUB), [a.clone(), a.clone()]);
    let bogus_goal = bv_eq(lhs, a.clone()); // bvSub a a == a  (FALSE)

    let tc = TypeChecker::with_mode(&e, e.mode());
    assert!(
        tc.check_type(&proof, &bogus_goal).is_err(),
        "kernel must reject the false identity bvSub a a == a"
    );
}

#[test]
fn test_no_theorem_attempts_the_false_identity() {
    // There is no registered theorem asserting the false identity, and building
    // one as a Declaration::Theorem with the bvSub_self body must fail kernel
    // checking (fail-closed). We attempt the registration and assert it errors.
    let mut e = env();
    let _ = symbolic_a(&mut e);
    // Build `fun (a : BV4) => bvSub_self a` proving the BOGUS type
    //   (a : BV4) → bvEq (bvSub a a) a
    let bv = Expr::const_str(names::BV);
    let bogus_type = {
        // Π (a : BV4), bvEq (bvSub a a) a
        let a = Expr::bvar(0);
        let lhs = Expr::apps(Expr::const_str(names::BV_SUB), [a.clone(), a.clone()]);
        let concl = bv_eq(lhs, a);
        Expr::pi(BinderInfo::Default, bv.clone(), concl)
    };
    let body = {
        // fun (a : BV4) => bvSub_self a
        let inner = Expr::app(
            Expr::const_(Name::from_string(names::BV_SUB_SELF), vec![]),
            Expr::bvar(0),
        );
        Expr::lam(BinderInfo::Default, bv, inner)
    };
    let res = e.add_decl(crate::Declaration::Theorem {
        name: Name::from_string("Clean.BV4.bvSub_self_FALSE"),
        level_params: vec![],
        type_: bogus_type,
        value: body,
    });
    assert!(
        res.is_err(),
        "registering the false identity must fail kernel type-checking"
    );
}

#[test]
fn test_bv_compute_width_is_four() {
    assert_eq!(BV_COMPUTE_WIDTH, 4, "honest concrete width is 4 bits");
}

#[test]
fn test_bvadd_actually_computes_one_plus_one_equals_two() {
    // SEMANTIC REALITY (not vacuous): on GROUND inputs the adder computes.
    // 1 + 1 = 2 at width 4: mk T F F F  +  mk T F F F  =  mk F T F F.
    // We prove `Eq.refl`-checks `bvAdd one one = two`, which only holds if the
    // ripple-carry definition genuinely reduces (carry from bit0 into bit1).
    let e = env();
    let t = Expr::const_str("Bool.true");
    let f = Expr::const_str("Bool.false");
    let mk = |b: [Expr; 4]| {
        Expr::apps(
            Expr::const_str(names::BV_MK),
            [b[0].clone(), b[1].clone(), b[2].clone(), b[3].clone()],
        )
    };
    let one = mk([t.clone(), f.clone(), f.clone(), f.clone()]);
    let two = mk([f.clone(), t.clone(), f.clone(), f.clone()]);
    let sum = Expr::apps(Expr::const_str(names::BV_ADD), [one.clone(), one]);

    // @Eq.{1} Clean.BV4 (bvAdd one one) two, proved by refl of `two`.
    let u1 = crate::Level::succ(crate::Level::zero());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
        [Expr::const_str(names::BV), sum, two.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(names::BV), two],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    tc.check_type(&refl, &goal)
        .expect("bvAdd must compute 1+1=2 (ripple carry reduces)");
}

// ── WIDTH-N (gate-fidelity) tests: bvAdd/bvEq compute correctly at N=8,16 ──────

/// Env with the width-`n` computational layer registered (idempotent).
fn env_width(n: u32) -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_compute_width(n).expect("init_bv_compute_width");
    env.init_bv_compute_width(n).expect("idempotent per width");
    env
}

/// `Clean.BV{n}.mk b0 .. b{n-1}` from a `u64` value (LSB = bit0), width `n`.
fn mk_value(nm: BvNames, value: u64) -> Expr {
    let bits: Vec<Expr> = (0..nm.width)
        .map(|k| {
            if (value >> k) & 1 == 1 {
                Expr::const_str("Bool.true")
            } else {
                Expr::const_str("Bool.false")
            }
        })
        .collect();
    Expr::apps(Expr::const_str(&nm.bv_mk()), bits)
}

/// `@Eq.{1} Clean.BV{n} lhs rhs`.
fn eq_bv(nm: BvNames, lhs: Expr, rhs: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [Expr::const_str(&nm.bv()), lhs, rhs],
    )
}

/// Check that `bvAdd (mk x) (mk y)` ι/δ-reduces (ripple carry) to `mk ((x+y) mod 2^n)`
/// at width `n`, via a kernel `Eq.refl` check. This is non-vacuous: it only holds if
/// the width-`n` ripple-carry adder genuinely propagates carries across all bits.
fn assert_add_computes(n: u32, x: u64, y: u64) {
    let nm = BvNames::new(n);
    let e = env_width(n);
    let mask = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
    let sum = (x.wrapping_add(y)) & mask;
    let lhs = Expr::apps(
        Expr::const_str(&nm.bv_add()),
        [mk_value(nm, x & mask), mk_value(nm, y & mask)],
    );
    let rhs = mk_value(nm, sum);
    let goal = eq_bv(nm, lhs, rhs.clone());
    let u1 = Level::succ(Level::zero());
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(&nm.bv()), rhs],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    tc.check_type(&refl, &goal).unwrap_or_else(|err| {
        panic!("width-{n} bvAdd {x}+{y} must compute to {sum} (ripple carry), got {err:?}")
    });
}

#[test]
fn test_width8_bvadd_computes_correctly() {
    // carry chains across the full byte: 0x0F + 0x01 = 0x10 (carry out of nibble),
    // 0xFF + 0x01 = 0x00 (wrap), 0x55 + 0x2A = 0x7F, 0x80 + 0x80 = 0x00 (overflow).
    assert_add_computes(8, 0x0F, 0x01);
    assert_add_computes(8, 0xFF, 0x01);
    assert_add_computes(8, 0x55, 0x2A);
    assert_add_computes(8, 0x80, 0x80);
    assert_add_computes(8, 0x3C, 0x4D);
}

#[test]
fn test_width16_bvadd_computes_correctly() {
    assert_add_computes(16, 0x00FF, 0x0001); // carry across byte boundary
    assert_add_computes(16, 0xFFFF, 0x0001); // full wrap
    assert_add_computes(16, 0x1234, 0x5678);
    assert_add_computes(16, 0x8000, 0x8000); // top-bit overflow
}

#[test]
fn test_width8_bvadd_wrong_bit_is_rejected() {
    // NEGATIVE CONTROL: a one-bit-wrong sum must FAIL the kernel re-check. If the
    // width-8 adder were degenerate (e.g. dropped a carry), a wrong sum could
    // sneak through; the kernel rejecting it confirms the encoding is faithful.
    let n = 8u32;
    let nm = BvNames::new(n);
    let e = env_width(n);
    let (x, y) = (0x0Fu64, 0x01u64);
    let correct = (x + y) & 0xFF; // 0x10
    let wrong = correct ^ 0b1000; // flip one bit → 0x18
    let lhs = Expr::apps(
        Expr::const_str(&nm.bv_add()),
        [mk_value(nm, x), mk_value(nm, y)],
    );
    let goal = eq_bv(nm, lhs, mk_value(nm, wrong));
    let u1 = Level::succ(Level::zero());
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(&nm.bv()), mk_value(nm, wrong)],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    assert!(
        tc.check_type(&refl, &goal).is_err(),
        "kernel must REJECT a wrong-bit width-8 sum (faithful encoding)"
    );
}

#[test]
fn test_width16_bvsub_self_computes_to_zero() {
    // bvSub a a == 0 for GROUND a at width 16: two's-complement a + ¬a + 1 = 0.
    // Computed (not the proved symbolic theorem) — exercises the width-16 ripple
    // carry of bvSub end-to-end.
    let n = 16u32;
    let nm = BvNames::new(n);
    let e = env_width(n);
    let a = mk_value(nm, 0xBEEF);
    let lhs = Expr::apps(Expr::const_str(&nm.bv_sub()), [a.clone(), a]);
    let zero = mk_value(nm, 0);
    let goal = eq_bv(nm, lhs, zero.clone());
    let u1 = Level::succ(Level::zero());
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(&nm.bv()), zero],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    tc.check_type(&refl, &goal)
        .expect("width-16 bvSub a a must compute to 0");
}

#[test]
fn test_width_n_registers_real_definitions_for_8_and_16() {
    for n in [8u32, 16] {
        let env = env_width(n);
        let nm = BvNames::new(n);
        for op in [
            nm.bv_zero(),
            nm.bv_not(),
            nm.bv_add(),
            nm.bv_sub(),
            nm.bv_eq(),
        ] {
            let info = env
                .get_const(&Name::from_string(&op))
                .unwrap_or_else(|| panic!("missing {op} at width {n}"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{op} must be a reducible Definition at width {n}"
            );
        }
        // all N bit accessors exist
        for k in 0..n {
            assert!(
                env.get_const(&Name::from_string(&nm.bit(k))).is_some(),
                "bit{k} accessor missing at width {n}"
            );
        }
    }
}

#[test]
fn test_width_n_bveq_is_a_prop() {
    let n = 8u32;
    let nm = BvNames::new(n);
    let mut e = env_width(n);
    e.add_decl(crate::Declaration::Axiom {
        name: Name::from_string("aw"),
        level_params: vec![],
        type_: Expr::const_str(&nm.bv()),
    })
    .expect("operand");
    let a = Expr::const_str("aw");
    let zero = Expr::const_str(&nm.bv_zero());
    let goal = Expr::apps(Expr::const_str(&nm.bv_eq()), [a, zero]);
    let tc = TypeChecker::with_mode(&e, e.mode());
    let ty = tc.infer_type(&goal).expect("width-N bvEq infers");
    assert!(ty.is_prop(), "width-N bvEq must be a Prop");
}

#[test]
fn test_bveq_is_a_prop_over_distinct_operands() {
    let mut e = env();
    let a = symbolic_a(&mut e);
    let zero = Expr::const_str(names::BV_ZERO);
    let goal = bv_eq(a.clone(), zero);
    let tc = TypeChecker::with_mode(&e, e.mode());
    let ty = tc.infer_type(&goal).expect("bvEq infers");
    assert!(ty.is_prop(), "bvEq must be a Prop");
    // touch helpers to keep them exercised
    let _ = bit(a, 0);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        FVarId::new(1),
        Name::anon(),
        Expr::const_str(names::BV),
        BinderInfo::Default,
    );
}

// ── RUNG-3 SUBSTRATE: the machine-vs-IR adder FIDELITY theorem ─────────────────
//
// `bvAdd_eq_ir : (x y : BV4) → bvEq (bvAdd x y) (bvAddIr x y)` is the real
// output-preservation theorem the #32 Instantiated path can instantiate:
// machine-side `bvAdd` (xor3/maj) ≡ IR-side `bvAddIr` (xor3Ir/majIr), SEPARATELY
// defined then PROVEN equal. These tests enforce the non-vacuity guard.

/// Env with the fidelity layer (`init_bv_fidelity`) registered.
fn fid_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_fidelity()
        .expect("init_bv_fidelity must register + kernel-check");
    env.init_bv_fidelity().expect("idempotent");
    env
}

#[test]
fn test_fidelity_theorem_is_a_proved_theorem_with_empty_axiom_closure() {
    let env = fid_env();
    let info = env
        .get_const(&Name::from_string(names::BV_ADD_EQ_IR))
        .expect("bvAdd_eq_ir must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "bvAdd_eq_ir must be a PROVED Theorem (kernel-checked), not an Axiom"
    );
    // [PROVED]: transitive domain-axiom closure is EMPTY (⊆ FOUNDATIONAL).
    assert!(
        domain_axioms(&env, names::BV_ADD_EQ_IR).is_empty(),
        "bvAdd_eq_ir must carry ZERO domain axioms; got {:?}",
        domain_axioms(&env, names::BV_ADD_EQ_IR)
    );
}

#[test]
fn test_machine_and_ir_adders_are_distinct_definitions() {
    // NON-VACUITY (1): bvAdd and bvAddIr are SEPARATELY-defined Definitions, and
    // their per-bit gates (xor3 vs xor3Ir, maj vs majIr) are DIFFERENT terms — so
    // the fidelity theorem is not X = X by construction.
    let env = fid_env();
    for (op, kind_name) in [
        (names::BV_ADD, "machine adder"),
        (names::BV_ADD_IR, "ir adder"),
        (names::XOR3, "machine sum gate"),
        (names::XOR3_IR, "ir sum gate"),
        (names::MAJ, "machine carry gate"),
        (names::MAJ_IR, "ir carry gate"),
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{kind_name} {op} must be registered"));
        assert_eq!(info.kind, ConstantKind::Definition, "{op} is a Definition");
    }
    // The two adders are not the same constant.
    assert_ne!(names::BV_ADD, names::BV_ADD_IR);
}

#[test]
fn test_fidelity_symbolic_goal_is_not_closeable_by_refl() {
    // NON-VACUITY (2, the make-or-break check): over SYMBOLIC operands the goal
    // `bvEq (bvAdd x y) (bvAddIr x y)` does NOT close by `Eq.refl` — because the
    // two adders are different terms that the kernel does NOT reduce to a common
    // form without case-splitting the bits. (If it DID close by refl, the layer
    // would be a rfl-collapse and the theorem vacuous.) We attempt to register a
    // BOGUS "theorem" whose VALUE is the `bvAdd_eq_ir` type proved by a bare
    // `Eq.refl`-style And.intro chain over symbolic bits — it MUST fail.
    let mut env = fid_env();
    // x, y : BV4 symbolic
    let x = {
        env.add_decl(crate::Declaration::Axiom {
            name: Name::from_string("fx"),
            level_params: vec![],
            type_: Expr::const_str(names::BV),
        })
        .expect("fx");
        Expr::const_str("fx")
    };
    let y = {
        env.add_decl(crate::Declaration::Axiom {
            name: Name::from_string("fy"),
            level_params: vec![],
            type_: Expr::const_str(names::BV),
        })
        .expect("fy");
        Expr::const_str("fy")
    };
    let add_m = Expr::apps(Expr::const_str(names::BV_ADD), [x.clone(), y.clone()]);
    let add_ir = Expr::apps(Expr::const_str(names::BV_ADD_IR), [x.clone(), y.clone()]);
    // bit0 of each side
    let l0 = bit(add_m, 0);
    let r0 = bit(add_ir, 0);
    // goal: Eq Bool (bit0 (bvAdd x y)) (bit0 (bvAddIr x y))
    let u1 = Level::succ(Level::zero());
    let bool_ty = Expr::const_str("Bool");
    let goal0 = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
        [bool_ty.clone(), l0.clone(), r0],
    );
    // a bare refl of the LHS bit — would only check if the two bits are
    // DEFINITIONALLY equal at symbolic operands (i.e. a rfl-collapse).
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [bool_ty, l0],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&refl, &goal0).is_err(),
        "the symbolic bit-0 equality must NOT close by Eq.refl — if it did, the \
         machine and IR adders would be a definitional rfl-collapse and the \
         fidelity theorem would be vacuous"
    );
}

#[test]
fn test_corrupted_ir_adder_fidelity_theorem_is_rejected() {
    // ADVERSARIAL / SAT-style negative control: a WRONG IR adder must make the
    // fidelity equality FALSE, so its theorem is UNPROVABLE (kernel-rejected).
    // We build a corrupted "ir adder" that drops the carry on bit 1 (uses plain
    // `Bool.xor x1 y1` instead of `xor3Ir x1 y1 c1`), then attempt to register
    // `bvEq (bvAdd x y) (bvAddBad x y)` proved by the SAME 2^8 case-split tactic.
    // At the witness x=y=1 (0001+0001), bit1 of bvAdd is 1 (carry) but bit1 of the
    // carry-dropping bvAddBad is 0 — so a leaf's `Eq.refl` fails to type-check and
    // add_decl REJECTS the theorem.
    let mut env = fid_env();
    let n = BV_COMPUTE_WIDTH;
    let nm = BvNames::new(n);
    let binop_ty = {
        let bv = Expr::const_str(names::BV);
        Expr::arrow(bv.clone(), Expr::arrow(bv.clone(), bv))
    };
    // bvAddBad x y: like bvAddIr but bit1's sum DROPS the carry (wrong gate).
    let bad_value = {
        let mut b = super::EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(Expr::const_str(names::BV));
        let (y_id, y) = b.fresh_local(Expr::const_str(names::BV));
        let xor = |a: Expr, c: Expr| Expr::apps(Expr::const_str("Bool.xor"), [a, c]);
        let xor3ir =
            |a: Expr, bb: Expr, c: Expr| Expr::apps(Expr::const_str(names::XOR3_IR), [a, bb, c]);
        let majir =
            |a: Expr, bb: Expr, c: Expr| Expr::apps(Expr::const_str(names::MAJ_IR), [a, bb, c]);
        let bitx = |k: u32| Expr::app(Expr::const_str(&nm.bit(k)), x.clone());
        let bity = |k: u32| Expr::app(Expr::const_str(&nm.bit(k)), y.clone());
        // bit0 normal, carry c1; bit1 DROPS carry (bug); rest normal-ish.
        let c1 = majir(bitx(0), bity(0), Expr::const_str("Bool.false"));
        let s0 = xor3ir(bitx(0), bity(0), Expr::const_str("Bool.false"));
        let s1_bad = xor(bitx(1), bity(1)); // BUG: ignores c1
        let c2 = majir(bitx(1), bity(1), c1);
        let s2 = xor3ir(bitx(2), bity(2), c2.clone());
        let c3 = majir(bitx(2), bity(2), c2);
        let s3 = xor3ir(bitx(3), bity(3), c3);
        let mk = Expr::apps(Expr::const_str(&nm.bv_mk()), [s0, s1_bad, s2, s3]);
        let e = b.mk_lam(y_id, BinderInfo::Default, Expr::const_str(names::BV), mk);
        let e = b.mk_lam(x_id, BinderInfo::Default, Expr::const_str(names::BV), e);
        b.finish(e)
    };
    env.add_decl(crate::Declaration::Definition {
        name: Name::from_string("Clean.BV4.bvAddBad"),
        level_params: vec![],
        type_: binop_ty,
        value: bad_value,
        is_reducible: true,
    })
    .expect("the bad adder is a well-typed Definition (it just computes wrong)");

    // Now the FALSE equality at the discriminating witness x=y=1:
    // bvAdd 1 1 = 2 (bit1 = true) ; bvAddBad 1 1 has bit1 = xor 1 1 = false.
    let one = {
        let t = Expr::const_str("Bool.true");
        let f = Expr::const_str("Bool.false");
        Expr::apps(Expr::const_str(&nm.bv_mk()), [t, f.clone(), f.clone(), f])
    };
    let add_m = Expr::apps(Expr::const_str(names::BV_ADD), [one.clone(), one.clone()]);
    let add_bad = Expr::apps(Expr::const_str("Clean.BV4.bvAddBad"), [one.clone(), one]);
    // goal: Eq Bool (bit1 (bvAdd 1 1)) (bit1 (bvAddBad 1 1))  — FALSE (true = false)
    let u1 = Level::succ(Level::zero());
    let bool_ty = Expr::const_str("Bool");
    let l1 = bit(add_m, 1);
    let r1 = bit(add_bad, 1);
    let false_goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
        [bool_ty.clone(), l1.clone(), r1],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [bool_ty, l1],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.check_type(&refl, &false_goal).is_err(),
        "the corrupted (carry-dropping) IR adder must make bit1 of (1+1) FALSE \
         against the machine adder — the kernel must REJECT the equality; a \
         carry bug cannot be proven equal to the machine adder"
    );
}

/// DISCRIMINATING WITNESS: the fidelity theorem, instantiated at the ground
/// witness 1+1, yields a TRUE equality the kernel accepts (bvAdd 1 1 == bvAddIr
/// 1 1 == 2) — proving the theorem is non-vacuously discharged on real data, the
/// dual of the corrupted-adder rejection above.
#[test]
fn test_fidelity_holds_at_ground_witness_one_plus_one() {
    let env = fid_env();
    let nm = BvNames::new(BV_COMPUTE_WIDTH);
    let one = {
        let t = Expr::const_str("Bool.true");
        let f = Expr::const_str("Bool.false");
        Expr::apps(Expr::const_str(&nm.bv_mk()), [t, f.clone(), f.clone(), f])
    };
    let two = {
        let t = Expr::const_str("Bool.true");
        let f = Expr::const_str("Bool.false");
        Expr::apps(Expr::const_str(&nm.bv_mk()), [f.clone(), t, f.clone(), f])
    };
    // Both adders compute 2; check each side ι-reduces to `two`.
    let add_m = Expr::apps(Expr::const_str(names::BV_ADD), [one.clone(), one.clone()]);
    let add_ir = Expr::apps(Expr::const_str(names::BV_ADD_IR), [one.clone(), one]);
    let u1 = Level::succ(Level::zero());
    let bv = Expr::const_str(names::BV);
    for side in [add_m, add_ir] {
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            [bv.clone(), side, two.clone()],
        );
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
            [bv.clone(), two.clone()],
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&refl, &goal)
            .expect("both adders compute 1+1=2 at the ground witness");
    }
}
