// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the PROVED Farkas (LRA) soundness layer.

use super::{names, proof_names};
use crate::name::Name;
use crate::{ConstantKind, Environment, Expr, Level, TypeChecker};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_farkas_soundness().expect("init_farkas_soundness");
    env.init_farkas_soundness().expect("idempotent");
    env
}

fn proofs_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_farkas_proofs().expect("init_farkas_proofs");
    env.init_farkas_proofs().expect("idempotent");
    env
}

/// Non-foundational axioms reachable from `name`.
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

fn assert_proved_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "{name} must be a Theorem; got {:?}",
        info.kind
    );
    let axs = domain_axioms(env, name);
    assert!(
        axs.is_empty(),
        "{name} must have empty domain-axiom closure; got {axs:?}"
    );
}

fn mul_tower_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_farkas_mul_tower().expect("init_farkas_mul_tower");
    env.init_farkas_mul_tower().expect("idempotent");
    env
}

fn structural_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_farkas_structural()
        .expect("init_farkas_structural");
    env.init_farkas_structural().expect("idempotent");
    env
}

// ── concrete-data builders ─────────────────────────────────────────────────

fn nat_lit(k: u32) -> Expr {
    let mut e = Expr::const_str("Nat.zero");
    for _ in 0..k {
        e = Expr::app(Expr::const_str("Nat.succ"), e);
    }
    e
}
fn int_ty() -> Expr {
    Expr::const_str(names::INT)
}
fn list_int() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]),
        int_ty(),
    )
}
fn list_list_int() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]),
        list_int(),
    )
}
/// `Int.mk |k| 0` for k≥0, `Int.mk 0 |k|` for k<0.
fn int_lit(k: i64) -> Expr {
    let mk = Expr::const_str(names::INT_MK);
    if k >= 0 {
        Expr::apps(mk, [nat_lit(u32::try_from(k).unwrap()), nat_lit(0)])
    } else {
        Expr::apps(mk, [nat_lit(0), nat_lit(u32::try_from(-k).unwrap())])
    }
}
fn nil_int() -> Expr {
    Expr::app(
        Expr::const_(
            Name::from_string("List.nil"),
            vec![Level::succ(Level::zero())],
        ),
        int_ty(),
    )
}
fn cons_int(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("List.cons"),
            vec![Level::succ(Level::zero())],
        ),
        [int_ty(), h, t],
    )
}
fn ints(xs: &[i64]) -> Expr {
    let mut e = nil_int();
    for &x in xs.iter().rev() {
        e = cons_int(int_lit(x), e);
    }
    e
}
fn nil_list_int() -> Expr {
    Expr::app(
        Expr::const_(
            Name::from_string("List.nil"),
            vec![Level::succ(Level::zero())],
        ),
        list_int(),
    )
}
fn cons_list_int(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("List.cons"),
            vec![Level::succ(Level::zero())],
        ),
        [list_int(), h, t],
    )
}
fn rows(rs: &[&[i64]]) -> Expr {
    let mut e = nil_list_int();
    for r in rs.iter().rev() {
        e = cons_list_int(ints(r), e);
    }
    e
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn farkas_checks(rows_e: Expr, bounds_e: Expr, mults_e: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(names::FARKAS_CHECKS),
        [rows_e, bounds_e, mults_e],
    )
}

// The infeasible instance from m5:  x ≤ -1 and -x ≤ -1, mults y = (1,1).
fn infeasible_rows() -> Expr {
    rows(&[&[1], &[-1]])
}
fn infeasible_bounds() -> Expr {
    ints(&[-1, -1])
}
fn good_mults() -> Expr {
    ints(&[1, 1])
}

fn whnf(env: &Environment, e: &Expr) -> Expr {
    let tc = TypeChecker::with_mode(env, env.mode());
    tc.whnf(e)
}

// ── structural / substrate tests ───────────────────────────────────────────

#[test]
fn test_substrate_definitions_kernel_check() {
    // Building env runs add_decl (kernel-checking each body against its type);
    // if any failed, init would have returned Err. Confirm the key constants
    // are present with the expected kinds.
    let env = env();
    for n in [
        names::INT_POS,
        names::INT_NEG,
        names::NAT_ADD,
        names::NAT_MUL,
        names::NAT_LE,
        names::INT_ADD,
        names::INT_MUL,
        names::INT_LE,
        names::HEAD_Z,
        names::TAIL_Z,
        names::INT_LIST_ADD,
        names::INT_LIST_SCALE,
        names::ALL_EQ_ZERO,
        names::COMBINE_COLUMNS,
        names::INT_DOT,
        names::ALL_NONNEG,
        names::FARKAS_CHECKS,
        names::ROWS_HOLD,
        names::UNSAT,
    ] {
        let info = env
            .get_const(&Name::from_string(n))
            .unwrap_or_else(|| panic!("{n} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{n} must be a Definition; got {:?}",
            info.kind
        );
    }
    assert!(
        env.get_inductive(&Name::from_string(names::INT)).is_some(),
        "the difference-pair Int inductive must be registered"
    );
}

#[test]
fn test_int_arithmetic_probes_compute() {
    // Probe intAdd/intMul/intLt/intLe/intEqZero/intIsNeg on concrete signed
    // inputs via semantic equality (the rep is non-normalized).
    let env = env();
    let z = int_lit;
    let int_eq = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::INT_EQ), [a, b]);
    let probe_eq = |a: Expr, b: Expr| whnf(&env, &int_eq(a, b)) == btrue();
    let iadd = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::INT_ADD), [a, b]);
    let imul = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::INT_MUL), [a, b]);
    let ilt = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::INT_LT), [a, b]);
    let ile = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::INT_LE), [a, b]);
    let isneg = |a: Expr| Expr::app(Expr::const_str(names::INT_IS_NEG), a);

    assert!(probe_eq(iadd(z(2), z(3)), z(5)), "2+3=5");
    assert!(probe_eq(iadd(z(2), z(-3)), z(-1)), "2+(-3)=-1");
    assert!(probe_eq(imul(z(2), z(3)), z(6)), "2*3=6");
    assert!(probe_eq(imul(z(2), z(-3)), z(-6)), "2*(-3)=-6");
    assert!(probe_eq(imul(z(-2), z(-3)), z(6)), "(-2)*(-3)=6");
    assert_eq!(whnf(&env, &ilt(z(-1), z(1))), btrue(), "-1<1");
    assert_eq!(whnf(&env, &ilt(z(1), z(1))), bfalse(), "1<1 false");
    assert_eq!(whnf(&env, &ile(z(1), z(1))), btrue(), "1≤1");
    assert_eq!(whnf(&env, &ile(z(2), z(1))), bfalse(), "2≤1 false");
    assert_eq!(whnf(&env, &isneg(z(-2))), btrue(), "isNeg -2");
    assert_eq!(whnf(&env, &isneg(z(0))), bfalse(), "isNeg 0 false");
}

#[test]
fn test_farkas_checks_sound_type_is_well_formed_prop() {
    // The headline soundness-bridge TYPE kernel-checks to Prop in clean's real
    // kernel — the certificate STRUCTURE is in the kernel. (The multiplicative
    // half of the *proof* is the precise remaining obligation; see module note.)
    use crate::Level;
    let env = env();
    let ty = super::farkas_checks_sound_type();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let sort = tc
        .infer_sort(&ty)
        .expect("farkasChecks_sound TYPE must kernel-check to a sort");
    assert_eq!(
        sort,
        Level::zero(),
        "soundness-bridge type must live in Prop (Sort 0)"
    );
}

#[test]
fn test_farkas_checks_sound_is_not_registered_as_a_proof() {
    // HONEST-STATUS GUARD. The top-level bridge `farkasChecks_sound` is NOT proved:
    // only its TYPE is built (see the test above). Assert the proof term is genuinely
    // absent from a fully-initialized env so the "PROVED arithmetic, STATED bridge"
    // accounting cannot silently rot into a faked registration. If/when the
    // multiplicative tower is finished and `farkasChecks_sound` is registered as a
    // real foundational Theorem, this test is updated to assert its proved status
    // instead (it must never be admitted via an axiom/unchecked path).
    let env = proofs_env();
    assert!(
        env.get_const(&Name::from_string(names::FARKAS_CHECKS_SOUND))
            .is_none(),
        "farkasChecks_sound must NOT be registered (it is not proved); only its TYPE \
         is built by farkas_checks_sound_type. A present const here would be an overclaim."
    );
}

// ── NON-VACUITY: infeasible passes, feasible/bogus fail ────────────────────

#[test]
fn test_nonvacuity_infeasible_system_passes_checker() {
    // THE HEADLINE non-vacuity witness: the concrete m5 infeasible system + its
    // valid Farkas cert reduce farkasChecks to Bool.true. So Unsat is provable
    // for a real infeasible system — the soundness theorem is NOT vacuous.
    let env = env();
    let app = farkas_checks(infeasible_rows(), infeasible_bounds(), good_mults());
    assert_eq!(
        whnf(&env, &app),
        btrue(),
        "infeasible system + valid cert must pass farkasChecks"
    );
}

#[test]
fn test_nonvacuity_feasible_system_fails_checker() {
    // A FEASIBLE system (-1 ≤ x ≤ 1, satisfied by x=0): rows [[1],[-1]], bounds
    // [1,1]. Same cert y=(1,1) cancels columns but Σ y b = 2 ≥ 0, so the checker
    // REJECTS. A feasible system does NOT satisfy farkasChecks=true.
    let env = env();
    let feasible_bounds = ints(&[1, 1]);
    let app = farkas_checks(infeasible_rows(), feasible_bounds, good_mults());
    assert_ne!(
        whnf(&env, &app),
        btrue(),
        "a feasible system must NOT pass farkasChecks"
    );
}

// ── PROVED arithmetic lemmas ───────────────────────────────────────────────

#[test]
fn test_nat_additive_bedrock_are_proved_theorems_foundational() {
    let env = proofs_env();
    for n in [
        proof_names::NAT_ADD_ZERO_L,
        proof_names::NAT_ADD_SUCC_L,
        proof_names::NAT_ADD_COMM,
        proof_names::NAT_ADD_ASSOC,
        proof_names::NAT_LE_REFL,
        proof_names::NAT_LE_ADD_R,
        proof_names::NAT_LE_TRANS,
        proof_names::NAT_LE_ADD_L,
        proof_names::NAT_LE_ADD_BOTH,
    ] {
        assert_proved_theorem(&env, n);
    }
}

#[test]
fn test_nat_le_contra_is_proved_theorem_foundational() {
    let env = proofs_env();
    assert_proved_theorem(&env, proof_names::NAT_LE_CONTRA);
}

#[test]
fn test_le_neg_false_is_proved_theorem_foundational() {
    let env = proofs_env();
    assert_proved_theorem(&env, proof_names::LE_NEG_FALSE);
}

#[test]
fn test_le_neg_false_is_proved_theorem_with_empty_domain_axioms() {
    // Mirrors resolution_soundness's
    // test_check_refutes_sound_is_proved_theorem_with_empty_domain_axioms: the
    // load-bearing endpoint contradiction `0 ≤ d < 0 → False` is a PROVED
    // kernel Theorem with ZERO residual domain-specific axioms (closure ⊆
    // FOUNDATIONAL — and in fact uses no Quot/propext, the substrate is
    // Quot-free).
    let env = proofs_env();
    let info = env
        .get_const(&Name::from_string(proof_names::LE_NEG_FALSE))
        .expect("leNegFalse registered");
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "leNegFalse must be a PROVED Theorem, not a stated Axiom"
    );
    let axs = domain_axioms(&env, proof_names::LE_NEG_FALSE);
    assert!(
        axs.is_empty(),
        "leNegFalse must have empty domain-axiom closure; got {axs:?}"
    );
}

#[test]
fn test_int_arith_lemmas_are_proved_theorems_foundational() {
    let env = proofs_env();
    for n in [
        proof_names::NAT_ADD_RESHUFFLE,
        proof_names::NAT_ADD_RESHUFFLE2,
        proof_names::NAT_LE_ADD_CANCEL_R,
        proof_names::INT_ADD_MONO,
        proof_names::INT_LE_TRANS,
    ] {
        assert_proved_theorem(&env, n);
    }
}

#[test]
fn test_nat_le_mul_mono_r_is_proved_theorem_foundational() {
    let env = proofs_env();
    assert_proved_theorem(&env, proof_names::NAT_LE_MUL_MONO_R);
}

// ── CONCRETE soundness fragment: m5UnsatConcrete ───────────────────────────

#[test]
fn test_m5_unsat_concrete_is_proved_theorem_foundational() {
    // The concrete proved infeasibility `Unsat [[1],[-1]] [-1,-1]` is a genuine
    // kernel-checked `Declaration::Theorem` with ZERO residual domain-specific
    // axioms (transitive closure ⊆ FOUNDATIONAL — and in fact Quot-free). This
    // is the clean-side parallel of the software kingdom's `emptyClauseUnsat`.
    let env = proofs_env();
    assert_proved_theorem(&env, proof_names::M5_UNSAT_CONCRETE);
}

#[test]
fn test_nat_mul_tower_are_proved_theorems_foundational() {
    // STEP 2 progress: the genuine Nat multiplicative lemmas toward the general
    // farkasChecks_sound (obligation (1)) are PROVED foundational Theorems.
    let env = mul_tower_env();
    for n in [
        proof_names::NAT_MUL_ZERO_L,
        proof_names::NAT_MUL_SUCC_L,
        proof_names::NAT_MUL_COMM,
        proof_names::NAT_MUL_DISTRIB_R,
    ] {
        assert_proved_theorem(&env, n);
    }
}

#[test]
fn test_int_structural_tower_are_proved_theorems_foundational() {
    // STEP 3 progress: the Int *equational* structural lemmas toward the general
    // farkasChecks_sound — intEta (structure eta), intAddZeroL, intAddAssoc, and
    // intMulDistribR (Int right-distributivity over the difference-pair rep) — are
    // genuine kernel-checked, axiom-free Theorems (transitive domain-axiom closure
    // EMPTY; Quot-free). These discharge the additive/distributive equational half
    // of obligation (3) in the module note.
    let env = structural_env();
    for n in [
        proof_names::INT_ETA,
        proof_names::INT_ADD_ZERO_L,
        proof_names::INT_ADD_ASSOC,
        proof_names::INT_MUL_DISTRIB_R,
    ] {
        assert_proved_theorem(&env, n);
    }
}

#[test]
fn test_m5_unsat_concrete_has_unsat_type() {
    // The theorem's TYPE is exactly `Unsat rows bounds` for the concrete m5
    // system — a real semantic infeasibility statement (∀ x, rowsHold → False),
    // not a vacuous restatement. Confirm the head of the type is `Unsat`.
    let env = proofs_env();
    let info = env
        .get_const(&Name::from_string(proof_names::M5_UNSAT_CONCRETE))
        .expect("m5UnsatConcrete registered");
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "m5UnsatConcrete must be a PROVED Theorem"
    );
    // The registered type must mention Unsat (the real model predicate).
    let head = info.type_.get_app_fn().clone();
    assert_eq!(
        head,
        Expr::const_str(names::UNSAT),
        "m5UnsatConcrete type head must be Clean.Farkas.Unsat; got {head:?}"
    );
}

#[test]
fn test_nonvacuity_negative_multiplier_fails() {
    let env = env();
    // y=(-1,1): not nonneg, columns don't cancel.
    let app = farkas_checks(infeasible_rows(), infeasible_bounds(), ints(&[-1, 1]));
    assert_ne!(whnf(&env, &app), btrue(), "negative multiplier rejected");
}

#[test]
fn test_nonvacuity_nonzero_column_sum_fails() {
    let env = env();
    // y=(2,1): nonneg but column sum 2*1 + 1*(-1) = 1 ≠ 0.
    let app = farkas_checks(infeasible_rows(), infeasible_bounds(), ints(&[2, 1]));
    assert_ne!(whnf(&env, &app), btrue(), "nonzero column sum rejected");
}
