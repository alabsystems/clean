// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::test_helpers::assert_const;
use super::*;
use crate::expr::{BinderInfo, ExprKind};

/// Helper: verify an inductive is registered with the expected name (without constructor check).
fn assert_ind(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let ind = env.get_inductive(&n).expect(name);
    assert_eq!(ind.name, n, "name mismatch for {name}");
}

/// Bug 4 Discriminating Test: Eq universe level in field types
///
/// This test verifies that Eq uses the correct universe level when applied
/// to α : Type u. Since Type u = Sort (u+1), and Eq.{v} : {α : Sort v} → ...,
/// we need Eq.{u+1} not Eq.{u}.
///
/// FAILS with old code: Eq.{u} when α : Type u
/// PASSES with fix: Eq.{u+1} when α : Type u
///
/// Re: #146 (Bug 4)
#[test]
fn test_bug4_eq_universe_level_discriminating() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    // AddSemigroup uses Eq in its add_assoc field
    env.init_add_semigroup().unwrap();

    let tc = TypeChecker::new(&env);

    // Get AddSemigroup.mk constructor type
    let mk_info = env
        .get_const(&Name::from_string("AddSemigroup.mk"))
        .expect("AddSemigroup.mk should exist");

    // This type check FAILS if Eq uses wrong universe level
    // Expected error (before fix): TypeMismatch { expected: Sort(Param("u")), inferred: Sort(Succ(Param("u"))) }
    let result = tc.infer_type(&mk_info.type_);

    assert!(
        result.is_ok(),
        "Bug 4 DISCRIMINATING TEST: AddSemigroup.mk type check failed.\n\
         This indicates Eq.{{u}} is used when Eq.{{u+1}} is needed.\n\
         When α : Type u (= Sort (u+1)), Eq needs universe u+1.\n\
         Error: {:?}",
        result.err()
    );
}

/// Bug 4 Discriminating Test: HAdd domain universe levels
///
/// HAdd.{u, v, w} : Type u → Type v → Type w → Type (max u v w)
///
/// When v and w params are 0, the domains should be Type 0 = Sort 1.
/// But if type_v = Sort v (instead of Sort (v+1)), we get Sort 0 = Prop.
///
/// FAILS with bug: HAdd.{0,0,0} expects Prop for β and γ, but Nat : Type 0
/// PASSES with fix: type_v and type_w use Sort (v+1) and Sort (w+1)
///
/// Re: #146 (Bug 4)
#[test]
fn test_bug4_hadd_universe_level_discriminating() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    // instHAddNat uses HAdd.{0,0,0}(Nat, Nat, Nat)
    env.init_nat_hadd_inst().unwrap();

    let tc = TypeChecker::new(&env);

    // Get instHAddNat type
    let inst_info = env
        .get_const(&Name::from_string("instHAddNat"))
        .expect("instHAddNat should exist");

    // This type check FAILS if HAdd domain uses Sort v instead of Sort (v+1)
    // Expected error (with bug): TypeMismatch { expected: Sort(Zero), inferred: Sort(Succ(Zero)) }
    // (expects Prop but Nat : Type 0 = Sort 1)
    let result = tc.infer_type(&inst_info.type_);

    assert!(
        result.is_ok(),
        "Bug 4 DISCRIMINATING TEST: instHAddNat type check failed.\n\
         This indicates HAdd domain types use Sort v instead of Sort (v+1).\n\
         In init_hadd: type_v should be Sort (v+1) = Type v, not Sort v.\n\
         Error: {:?}",
        result.err()
    );
}

/// Bug 4 Discriminating Test: Ne universe level in DivisionRing
///
/// Ne.{u} : {α : Sort u} → α → α → Prop (same as Eq)
///
/// When α : Type u, we need Ne.{u+1} not Ne.{u}.
/// The DivisionRing.mul_inv_cancel field uses Ne with wrong level.
///
/// FAILS with bug: Ne.{u} when α : Type u
/// PASSES with fix: Ne.{u+1} when α : Type u
///
/// Re: #146 (Bug 4)
#[test]
fn test_bug4_ne_universe_level_discriminating() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        // DivisionRing uses Ne in mul_inv_cancel field
        env.init_division_ring().unwrap();

        let tc = TypeChecker::new(&env);

        // Get DivisionRing.mk constructor type
        let mk_info = env
            .get_const(&Name::from_string("DivisionRing.mk"))
            .expect("DivisionRing.mk should exist");

        // This type check FAILS if Ne uses wrong universe level
        // Expected error (with bug): TypeMismatch { expected: Sort(Param("u")), inferred: Sort(Succ(Param("u"))) }
        let result = tc.infer_type(&mk_info.type_);

        assert!(
            result.is_ok(),
            "Bug 4 DISCRIMINATING TEST: DivisionRing.mk type check failed.\n\
             This indicates Ne.{{u}} is used when Ne.{{u+1}} is needed.\n\
             In field.rs: Ne should use Level::succ(u_level) not u_level.\n\
             Error: {:?}",
            result.err()
        );
    });
}

/// Run a test with a larger stack for tests involving deep type structures.
/// This is needed for tests involving DivisionRing, Field, IntegralDomain, etc.
fn with_large_stack<F: FnOnce() + Send + 'static>(f: F) {
    crate::test_utils::run_with_stack(crate::test_utils::MEDIUM_STACK, f);
}

fn assert_expr_has_type(
    tc: &crate::tc::TypeChecker<'_>,
    expr: &Expr,
    expected: &Expr,
    context: &str,
) {
    let inferred = tc
        .infer_type(expr)
        .unwrap_or_else(|e| panic!("{context} should type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, expected),
        "{context} type mismatch: inferred {inferred:?}, expected {expected:?}"
    );
}

fn assert_typeclass_constructor_shape(
    tc: &crate::tc::TypeChecker<'_>,
    ty: &Expr,
    expected_binders: usize,
    expected_head: &str,
    context: &str,
) {
    let inferred = tc
        .infer_type(ty)
        .unwrap_or_else(|e| panic!("{context} type should be well-formed: {e:?}"));
    assert!(
        matches!(&inferred.kind, ExprKind::Sort(_)),
        "{context} should infer to a sort, got {inferred:?}"
    );
    let (binders, codomain) = count_pi_binders(ty);
    assert_eq!(
        binders, expected_binders,
        "{context} should have {expected_binders} binders"
    );
    let head = expr_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some(expected_head),
        "{context} codomain head should be {expected_head}, got {head:?}"
    );
}

fn assert_typeclass_projection_shape(
    tc: &crate::tc::TypeChecker<'_>,
    ty: &Expr,
    expected_binders: usize,
    context: &str,
) {
    let inferred = tc
        .infer_type(ty)
        .unwrap_or_else(|e| panic!("{context} type should be well-formed: {e:?}"));
    assert!(
        matches!(&inferred.kind, ExprKind::Sort(_)),
        "{context} should infer to a sort, got {inferred:?}"
    );
    let (binders, codomain) = count_pi_binders(ty);
    assert_eq!(
        binders, expected_binders,
        "{context} should have {expected_binders} binders"
    );
    assert!(
        matches!(&codomain.kind, ExprKind::BVar(_)),
        "{context} codomain should be the carrier type, got {codomain:?}"
    );
}

fn assert_concrete_instance_shape(
    tc: &crate::tc::TypeChecker<'_>,
    ty: &Expr,
    value: Option<&Expr>,
    expected_head: &str,
    context: &str,
) {
    let inferred = tc
        .infer_type(ty)
        .unwrap_or_else(|e| panic!("{context} type should be well-formed: {e:?}"));
    assert!(
        matches!(&inferred.kind, ExprKind::Sort(_)),
        "{context} should infer to a sort, got {inferred:?}"
    );
    let (binders, codomain) = count_pi_binders(ty);
    assert_eq!(
        binders, 0,
        "{context} should be a concrete instance without binders"
    );
    let head = expr_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some(expected_head),
        "{context} type head should be {expected_head}, got {head:?}"
    );
    let value = value.unwrap_or_else(|| panic!("{context} should be defined with a value"));
    assert_expr_has_type(tc, value, ty, &format!("{context} value"));
}

#[test]
fn test_init_nat_hadd_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hadd_inst());

    env.init_nat_hadd_inst().unwrap();
    assert!(env.has_nat_hadd_inst());

    assert_const(&env, "instHAddNat");
}

#[test]
fn test_init_int_hadd_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_hadd_inst());

    env.init_int_hadd_inst().unwrap();
    assert!(env.has_int_hadd_inst());

    assert_const(&env, "instHAddInt");
}

#[test]
fn test_init_nat_hsub_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hsub_inst());

    env.init_nat_hsub_inst().unwrap();
    assert!(env.has_nat_hsub_inst());

    assert_const(&env, "instHSubNat");
}

#[test]
fn test_init_int_hsub_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_hsub_inst());

    env.init_int_hsub_inst().unwrap();
    assert!(env.has_int_hsub_inst());

    assert_const(&env, "instHSubInt");
}

#[test]
fn test_init_nat_hmul_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hmul_inst());

    env.init_nat_hmul_inst().unwrap();
    assert!(env.has_nat_hmul_inst());

    assert_const(&env, "instHMulNat");
}

#[test]
fn test_init_int_hmul_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_hmul_inst());

    env.init_int_hmul_inst().unwrap();
    assert!(env.has_int_hmul_inst());

    assert_const(&env, "instHMulInt");
}

// ---------------------------------------------------------------------------
// Track PP: Int HDiv/HMod instances backed by the Opaque Int.div / Int.mod
// constants from init_int_arith. `Opaque` is NOT `Axiom`, so the instances are
// axiom-free (empty axiom_deps) — the kernel-checked instance value
// `HDiv.mk Int Int Int Int.div` carries no axiom dependency.
// ---------------------------------------------------------------------------

/// The Int hetero instance must be a kernel-checkable `Definition` whose value
/// type-checks against its declared type, and must carry an EMPTY axiom
/// closure (Int.div / Int.mod are `Opaque`, not `Axiom`).
fn assert_int_hetero_inst_axiom_free(env: &Environment, projection: &str, instance: &str) {
    use crate::tc::TypeChecker;
    let tc = TypeChecker::new(env);

    let proj_info = env
        .get_const(&Name::from_string(projection))
        .unwrap_or_else(|| panic!("{projection} should exist"));
    let _ = tc
        .infer_type(&proj_info.type_)
        .unwrap_or_else(|e| panic!("{projection} type must type-check: {e:?}"));

    let inst_info = env
        .get_const(&Name::from_string(instance))
        .unwrap_or_else(|| panic!("{instance} should exist"));
    let _ = tc
        .infer_type(&inst_info.type_)
        .unwrap_or_else(|e| panic!("{instance} type must type-check: {e:?}"));
    if let Some(value) = inst_info.value.as_ref() {
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("{instance} value must type-check: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &inst_info.type_),
            "{instance} value type must be def-eq to declared type"
        );
    }

    let deps = env
        .axiom_deps(&Name::from_string(instance))
        .unwrap_or_default();
    assert!(
        deps.is_empty(),
        "{instance} must have an EMPTY axiom closure (Int.div/Int.mod are Opaque, not Axiom); deps = {deps:?}"
    );
}

#[test]
fn test_init_int_hdiv_inst() {
    let mut env = Environment::with_prelude();
    assert_const(&env, "instHDivInt");
    assert_const(&env, "Int.div");
    // Int.div must be Opaque (data), never an Axiom — so it never pollutes an
    // axiom closure.
    let info = env.get_const(&Name::from_string("Int.div")).unwrap();
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "Int.div must be Opaque, got {:?}",
        info.kind
    );
    assert_int_hetero_inst_axiom_free(&env, "HDiv.hDiv", "instHDivInt");
    // Idempotent.
    env.init_int_hdiv_inst().unwrap();
    assert_const(&env, "instHDivInt");
}

#[test]
fn test_init_int_hmod_inst() {
    let mut env = Environment::with_prelude();
    assert_const(&env, "instHModInt");
    assert_const(&env, "Int.mod");
    let info = env.get_const(&Name::from_string("Int.mod")).unwrap();
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "Int.mod must be Opaque, got {:?}",
        info.kind
    );
    assert_int_hetero_inst_axiom_free(&env, "HMod.hMod", "instHModInt");
    env.init_int_hmod_inst().unwrap();
    assert_const(&env, "instHModInt");
}

#[test]
fn test_int_hadd_hsub_hmul_axiom_free_in_prelude() {
    // The +/-/* Int instances reference the real Int.add/sub/mul Definitions
    // (Int.rec/Nat.rec bodies), so their axiom closure is empty.
    let env = Environment::with_prelude();
    assert_int_hetero_inst_axiom_free(&env, "HAdd.hAdd", "instHAddInt");
    assert_int_hetero_inst_axiom_free(&env, "HSub.hSub", "instHSubInt");
    assert_int_hetero_inst_axiom_free(&env, "HMul.hMul", "instHMulInt");
}

#[test]
fn test_init_int_hpow_inst() {
    // `(b : Int) ^ (n : Nat)` instance, backed by the real `Int.pow` Nat.rec
    // recursion. `Int.pow` is a Definition (data), and the instance closure is
    // axiom-free.
    let env = Environment::with_prelude();
    assert_const(&env, "instHPowIntNat");
    assert_const(&env, "Int.pow");
    let info = env.get_const(&Name::from_string("Int.pow")).unwrap();
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Int.pow must be a Definition, got {:?}",
        info.kind
    );
    assert_int_hetero_inst_axiom_free(&env, "HPow.hPow", "instHPowIntNat");
    // Int.pow itself is axiom-free.
    let deps = env
        .axiom_deps(&Name::from_string("Int.pow"))
        .unwrap_or_default();
    assert!(
        deps.is_empty(),
        "Int.pow must have an EMPTY axiom closure; deps = {deps:?}"
    );
}

// ---------------------------------------------------------------------------
// Track N: bitwise heterogeneous typeclass Nat instances
// (HAnd/HOr/HXor/HShiftLeft/HShiftRight backed by Nat.land/lor/xor/shiftLeft/
// shiftRight). These make `m &&& n`, `m ||| n`, `m ^^^ n`, `m <<< n`, `m >>> n`
// elaborate and compute for Nat.
// ---------------------------------------------------------------------------

/// Soundness helper: infer_type must succeed on the projection and the
/// instance for a bitwise hetero class (no malformed kernel terms).
fn assert_bitwise_inst_sound(env: &Environment, projection: &str, instance: &str) {
    use crate::tc::TypeChecker;
    let tc = TypeChecker::new(env);

    let proj_info = env
        .get_const(&Name::from_string(projection))
        .unwrap_or_else(|| panic!("{projection} should exist"));
    let _ = tc
        .infer_type(&proj_info.type_)
        .unwrap_or_else(|e| panic!("{projection} type must type-check: {e:?}"));

    let inst_info = env
        .get_const(&Name::from_string(instance))
        .unwrap_or_else(|| panic!("{instance} should exist"));
    let _ = tc
        .infer_type(&inst_info.type_)
        .unwrap_or_else(|e| panic!("{instance} type must type-check: {e:?}"));
    // The instance value (HXxx.mk Nat Nat Nat Nat.<op>) must also type-check
    // against its declared type.
    if let Some(value) = inst_info.value.as_ref() {
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("{instance} value must type-check: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &inst_info.type_),
            "{instance} value type {inferred:?} must be def-eq to declared type {:?}",
            inst_info.type_
        );
    }
}

/// Soundness helper: the instance must NOT pull in `sorryAx`, and its only
/// axiom dependency (if any) must be the named backing Nat function. The
/// Nat bitwise ops are themselves declared as axioms (arbitrary-precision
/// bitwise cannot be defined via Nat.rec alone); that pre-existing dependency
/// is expected, but nothing must launder a `sorryAx` in.
fn assert_no_sorry_only_backing(env: &Environment, instance: &str, backing: &str) {
    let deps = env
        .axiom_deps(&Name::from_string(instance))
        .unwrap_or_default();
    assert!(
        !deps.contains(&Name::from_string("sorryAx")),
        "{instance} must not depend on sorryAx; deps = {deps:?}"
    );
    for d in &deps {
        let s = d.to_string();
        assert!(
            s == backing,
            "{instance} unexpected axiom dependency {s:?} (only {backing:?} allowed)"
        );
    }
}

#[test]
fn test_init_nat_hand_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hand_inst());
    env.init_nat_hand_inst().unwrap();
    assert!(env.has_nat_hand_inst());
    assert_const(&env, "instHAndNat");
    assert_const(&env, "HAnd.hAnd");
    assert_bitwise_inst_sound(&env, "HAnd.hAnd", "instHAndNat");
    assert_no_sorry_only_backing(&env, "instHAndNat", "Nat.land");
    // Idempotent.
    env.init_nat_hand_inst().unwrap();
    assert!(env.has_nat_hand_inst());
}

#[test]
fn test_init_nat_hor_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hor_inst());
    env.init_nat_hor_inst().unwrap();
    assert!(env.has_nat_hor_inst());
    assert_const(&env, "instHOrNat");
    assert_const(&env, "HOr.hOr");
    assert_bitwise_inst_sound(&env, "HOr.hOr", "instHOrNat");
    assert_no_sorry_only_backing(&env, "instHOrNat", "Nat.lor");
}

#[test]
fn test_init_nat_hxor_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hxor_inst());
    env.init_nat_hxor_inst().unwrap();
    assert!(env.has_nat_hxor_inst());
    assert_const(&env, "instHXorNat");
    assert_const(&env, "HXor.hXor");
    assert_bitwise_inst_sound(&env, "HXor.hXor", "instHXorNat");
    assert_no_sorry_only_backing(&env, "instHXorNat", "Nat.xor");
}

#[test]
fn test_init_nat_hshiftleft_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hshiftleft_inst());
    env.init_nat_hshiftleft_inst().unwrap();
    assert!(env.has_nat_hshiftleft_inst());
    assert_const(&env, "instHShiftLeftNat");
    assert_const(&env, "HShiftLeft.hShiftLeft");
    assert_bitwise_inst_sound(&env, "HShiftLeft.hShiftLeft", "instHShiftLeftNat");
    // Nat.shiftLeft is a real Definition (not an axiom), so no axiom deps at all.
    let deps = env
        .axiom_deps(&Name::from_string("instHShiftLeftNat"))
        .unwrap_or_default();
    assert!(
        !deps.contains(&Name::from_string("sorryAx")),
        "instHShiftLeftNat must not depend on sorryAx; deps = {deps:?}"
    );
}

#[test]
fn test_init_nat_hshiftright_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_hshiftright_inst());
    env.init_nat_hshiftright_inst().unwrap();
    assert!(env.has_nat_hshiftright_inst());
    assert_const(&env, "instHShiftRightNat");
    assert_const(&env, "HShiftRight.hShiftRight");
    assert_bitwise_inst_sound(&env, "HShiftRight.hShiftRight", "instHShiftRightNat");
    assert_no_sorry_only_backing(&env, "instHShiftRightNat", "Nat.shiftRight");
}

/// Computation soundness: `@HAnd.hAnd Nat Nat Nat instHAndNat 6 3` reduces to
/// the Nat literal 2 (def-eq), exercising the same WHNF path that `clean check`
/// uses for `theorem t : (6 &&& 3 : Nat) = 2 := rfl`.
#[test]
fn test_bitwise_hetero_computation() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_hand_inst().unwrap();
    env.init_nat_hor_inst().unwrap();
    env.init_nat_hxor_inst().unwrap();
    env.init_nat_hshiftleft_inst().unwrap();
    env.init_nat_hshiftright_inst().unwrap();

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let cases: &[(&str, &str, u64, u64, u64)] = &[
        ("HAnd.hAnd", "instHAndNat", 6, 3, 2),
        ("HOr.hOr", "instHOrNat", 6, 3, 7),
        ("HXor.hXor", "instHXorNat", 6, 3, 5),
        ("HShiftLeft.hShiftLeft", "instHShiftLeftNat", 1, 4, 16),
        ("HShiftRight.hShiftRight", "instHShiftRightNat", 16, 2, 4),
    ];

    for (proj, inst, a, b, expected) in cases {
        let lhs = Expr::apps(
            Expr::const_(
                Name::from_string(proj),
                vec![Level::zero(), Level::zero(), Level::zero()],
            ),
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                Expr::const_(Name::from_string(inst), vec![]),
                Expr::nat_lit(*a),
                Expr::nat_lit(*b),
            ],
        );
        let rhs = Expr::nat_lit(*expected);
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "{proj} {a} {b} should be def-eq to {expected}"
        );
    }
}

/// `with_prelude` wires the bitwise instances and the bare `and`/`or` Bool
/// aliases used by the `&&`/`||` surface operators.
#[test]
fn test_prelude_has_bitwise_and_bool_aliases() {
    let env = Environment::with_prelude();
    assert_const(&env, "instHAndNat");
    assert_const(&env, "instHOrNat");
    assert_const(&env, "instHXorNat");
    assert_const(&env, "instHShiftLeftNat");
    assert_const(&env, "instHShiftRightNat");
    assert_const(&env, "and");
    assert_const(&env, "or");
}

#[test]
fn test_init_real_hmul_inst() {
    let mut env = Environment::new();
    assert!(!env.has_real_hmul_inst());

    env.init_real_hmul_inst().unwrap();
    assert!(env.has_real_hmul_inst());

    assert_const(&env, "instHMulReal");

    env.init_real_hmul_inst().unwrap();
    assert!(env.has_real_hmul_inst());
}

#[test]
fn test_init_real_neg_inst() {
    let mut env = Environment::new();
    assert!(!env.has_real_neg_inst());

    env.init_real_neg_inst().unwrap();
    assert!(env.has_real_neg_inst());

    assert_const(&env, "instNegReal");

    env.init_real_neg_inst().unwrap();
    assert!(env.has_real_neg_inst());
}

#[test]
fn test_heterogeneous_instances_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_hadd_inst().unwrap();
    env.init_int_hadd_inst().unwrap();
    env.init_nat_hsub_inst().unwrap();
    env.init_int_hsub_inst().unwrap();
    env.init_nat_hmul_inst().unwrap();
    env.init_int_hmul_inst().unwrap();

    let tc = TypeChecker::new(&env);

    for (name, expected_head) in [
        ("instHAddNat", "HAdd"),
        ("instHAddInt", "HAdd"),
        ("instHSubNat", "HSub"),
        ("instHSubInt", "HSub"),
        ("instHMulNat", "HMul"),
        ("instHMulInt", "HMul"),
    ] {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let type_of_type = tc
            .infer_type(&info.type_)
            .unwrap_or_else(|e| panic!("{name} type should type-check: {e:?}"));
        assert!(
            matches!(&type_of_type.kind, ExprKind::Sort(_)),
            "{name} declaration type should infer to a sort, got {type_of_type:?}"
        );

        let (binders, codomain) = count_pi_binders(&info.type_);
        assert_eq!(
            binders, 0,
            "{name} should be a concrete instance without binders"
        );
        let head = expr_head_const(&codomain);
        assert_eq!(
            head.as_deref(),
            Some(expected_head),
            "{name} type head should be {expected_head}, got {head:?}"
        );

        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should be defined with a value"));
        assert_expr_has_type(&tc, value, &info.type_, &format!("{name} value"));
    }
}

#[test]
fn test_heterogeneous_typeclasses_idempotent() {
    let mut env = Environment::new();

    // Initialize all heterogeneous typeclasses twice
    env.init_hadd().unwrap();
    env.init_hadd().unwrap();
    env.init_hsub().unwrap();
    env.init_hsub().unwrap();
    env.init_hmul().unwrap();
    env.init_hmul().unwrap();
    env.init_hdiv().unwrap();
    env.init_hdiv().unwrap();
    env.init_div().unwrap();
    env.init_div().unwrap();
    env.init_hmod().unwrap();
    env.init_hmod().unwrap();
    env.init_mod().unwrap();
    env.init_mod().unwrap();
    env.init_hpow().unwrap();
    env.init_hpow().unwrap();
    env.init_pow().unwrap();
    env.init_pow().unwrap();

    // Verify all flags are set
    assert!(env.has_hadd());
    assert!(env.has_hsub());
    assert!(env.has_hmul());
    assert!(env.has_hdiv());
    assert!(env.has_div());
    assert!(env.has_hmod());
    assert!(env.has_mod());
    assert!(env.has_hpow());
    assert!(env.has_pow());
}

#[test]
fn test_heterogeneous_registered_class_metadata() {
    let mut env = Environment::new();
    env.init_hadd().unwrap();
    env.init_hpow().unwrap();

    for class_name in ["HAdd", "HPow"] {
        let info = env
            .get_class_info(&Name::from_string(class_name))
            .unwrap_or_else(|| panic!("{class_name} should be registered as a class"));
        assert_eq!(
            info.num_params, 3,
            "{class_name} should expose three class parameters"
        );
        assert_eq!(
            info.out_params,
            vec![2],
            "{class_name} should mark the result type as out-parameter"
        );
    }
}

#[test]
fn test_heterogeneous_instances_idempotent() {
    let mut env = Environment::new();

    // Initialize all heterogeneous instances twice
    env.init_nat_hadd_inst().unwrap();
    env.init_nat_hadd_inst().unwrap();
    env.init_int_hadd_inst().unwrap();
    env.init_int_hadd_inst().unwrap();
    env.init_nat_hsub_inst().unwrap();
    env.init_nat_hsub_inst().unwrap();
    env.init_int_hsub_inst().unwrap();
    env.init_int_hsub_inst().unwrap();
    env.init_nat_hmul_inst().unwrap();
    env.init_nat_hmul_inst().unwrap();
    env.init_int_hmul_inst().unwrap();
    env.init_int_hmul_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_nat_hadd_inst());
    assert!(env.has_int_hadd_inst());
    assert!(env.has_nat_hsub_inst());
    assert!(env.has_int_hsub_inst());
    assert!(env.has_nat_hmul_inst());
    assert!(env.has_int_hmul_inst());
}

// ========================================================================
// Tests for Algebraic Structure Typeclasses (Semigroup, Monoid, etc.)
// ========================================================================

#[test]
fn test_semigroup_init() {
    let mut env = Environment::new();
    assert!(!env.has_semigroup());

    env.init_semigroup().unwrap();
    assert!(env.has_semigroup());

    // Verify Semigroup type exists
    assert_ind(&env, "Semigroup");
    assert_const(&env, "Semigroup.mk");
    assert_const(&env, "Semigroup.mul");
}

#[test]
fn test_add_semigroup_init() {
    let mut env = Environment::new();
    assert!(!env.has_add_semigroup());

    env.init_add_semigroup().unwrap();
    assert!(env.has_add_semigroup());

    // Verify AddSemigroup type exists
    assert_ind(&env, "AddSemigroup");
    assert_const(&env, "AddSemigroup.mk");
    assert_const(&env, "AddSemigroup.add");
}

#[test]
fn test_monoid_init() {
    let mut env = Environment::new();
    assert!(!env.has_monoid());

    env.init_monoid().unwrap();
    assert!(env.has_monoid());

    // Verify Monoid type exists
    assert_ind(&env, "Monoid");
    assert_const(&env, "Monoid.mk");
    assert_const(&env, "Monoid.mul");
    assert_const(&env, "Monoid.one");
}

#[test]
fn test_add_monoid_init() {
    let mut env = Environment::new();
    assert!(!env.has_add_monoid());

    env.init_add_monoid().unwrap();
    assert!(env.has_add_monoid());

    // Verify AddMonoid type exists
    assert_ind(&env, "AddMonoid");
    assert_const(&env, "AddMonoid.mk");
    assert_const(&env, "AddMonoid.add");
    assert_const(&env, "AddMonoid.zero");
}

#[test]
fn test_semigroup_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_semigroup().unwrap();

    let tc = TypeChecker::new(&env);

    // Check Semigroup.mk type
    let mk = env.get_const(&Name::from_string("Semigroup.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 3, "Semigroup", "Semigroup.mk");

    // Check Semigroup.mul type
    let mul_proj = env.get_const(&Name::from_string("Semigroup.mul")).unwrap();
    assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "Semigroup.mul");
}

#[test]
fn test_add_semigroup_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_add_semigroup().unwrap();

    let tc = TypeChecker::new(&env);

    // Check AddSemigroup.mk type
    let mk = env
        .get_const(&Name::from_string("AddSemigroup.mk"))
        .unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 3, "AddSemigroup", "AddSemigroup.mk");

    // Check AddSemigroup.add type
    let add_proj = env
        .get_const(&Name::from_string("AddSemigroup.add"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "AddSemigroup.add");
}

#[test]
fn test_monoid_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_monoid().unwrap();

    let tc = TypeChecker::new(&env);

    // Check Monoid.mk type
    let mk = env.get_const(&Name::from_string("Monoid.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 6, "Monoid", "Monoid.mk");

    // Check projections
    let mul_proj = env.get_const(&Name::from_string("Monoid.mul")).unwrap();
    assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "Monoid.mul");

    let one_proj = env.get_const(&Name::from_string("Monoid.one")).unwrap();
    assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "Monoid.one");
}

#[test]
fn test_add_monoid_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_add_monoid().unwrap();

    let tc = TypeChecker::new(&env);

    // Check AddMonoid.mk type
    let mk = env.get_const(&Name::from_string("AddMonoid.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 6, "AddMonoid", "AddMonoid.mk");

    // Check projections
    let add_proj = env.get_const(&Name::from_string("AddMonoid.add")).unwrap();
    assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "AddMonoid.add");

    let zero_proj = env.get_const(&Name::from_string("AddMonoid.zero")).unwrap();
    assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "AddMonoid.zero");
}

#[test]
fn test_nat_add_semigroup_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_add_semigroup_inst());

    env.init_nat_add_semigroup_inst().unwrap();
    assert!(env.has_nat_add_semigroup_inst());

    assert!(env
        .get_const(&Name::from_string("instAddSemigroupNat"))
        .is_some());
}

#[test]
fn test_int_add_semigroup_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_semigroup_inst());

    env.init_int_add_semigroup_inst().unwrap();
    assert!(env.has_int_add_semigroup_inst());

    assert!(env
        .get_const(&Name::from_string("instAddSemigroupInt"))
        .is_some());
}

#[test]
fn test_nat_add_monoid_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_add_monoid_inst());

    env.init_nat_add_monoid_inst().unwrap();
    assert!(env.has_nat_add_monoid_inst());

    assert!(env
        .get_const(&Name::from_string("instAddMonoidNat"))
        .is_some());
}

#[test]
fn test_int_add_monoid_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_monoid_inst());

    env.init_int_add_monoid_inst().unwrap();
    assert!(env.has_int_add_monoid_inst());

    let info = env
        .get_const(&Name::from_string("instAddMonoidInt"))
        .expect("instAddMonoidInt should exist");

    // instAddMonoidInt : AddMonoid Int (0 Pi binders — it's a concrete instance)
    let (binder_count, codomain) = count_pi_binders(&info.type_);
    assert_eq!(
        binder_count, 0,
        "instAddMonoidInt should have 0 binders (concrete instance)"
    );
    // Type should be `AddMonoid Int` — head const is AddMonoid
    let head = expr_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("AddMonoid"),
        "instAddMonoidInt type head should be AddMonoid"
    );
}

#[test]
fn test_algebraic_structure_instances_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_semigroup_inst().unwrap();
    env.init_int_add_semigroup_inst().unwrap();
    env.init_nat_add_monoid_inst().unwrap();
    env.init_int_add_monoid_inst().unwrap();

    let tc = TypeChecker::new(&env);

    // Each instance should type-check AND have the correct type-class head
    let expected_heads = [
        ("instAddSemigroupNat", "AddSemigroup"),
        ("instAddSemigroupInt", "AddSemigroup"),
        ("instAddMonoidNat", "AddMonoid"),
        ("instAddMonoidInt", "AddMonoid"),
    ];
    for (name, expected_class) in expected_heads {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert_concrete_instance_shape(&tc, &info.type_, info.value.as_ref(), expected_class, name);
    }
}

/// Extract the head constant name from an expression (walking through App nodes).
fn expr_head_const(expr: &Expr) -> Option<String> {
    use crate::expr::ExprKind;
    let mut cur = expr;
    loop {
        match &cur.kind {
            ExprKind::App(f, _) => cur = f.as_ref(),
            ExprKind::Const(name, _) => return Some(name.to_string()),
            _ => return None,
        }
    }
}

#[test]
fn test_algebraic_structure_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_semigroup().unwrap();
    env.init_semigroup().unwrap();
    env.init_add_semigroup().unwrap();
    env.init_add_semigroup().unwrap();
    env.init_monoid().unwrap();
    env.init_monoid().unwrap();
    env.init_add_monoid().unwrap();
    env.init_add_monoid().unwrap();
    env.init_nat_add_semigroup_inst().unwrap();
    env.init_nat_add_semigroup_inst().unwrap();
    env.init_int_add_semigroup_inst().unwrap();
    env.init_int_add_semigroup_inst().unwrap();
    env.init_nat_add_monoid_inst().unwrap();
    env.init_nat_add_monoid_inst().unwrap();
    env.init_int_add_monoid_inst().unwrap();
    env.init_int_add_monoid_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_semigroup());
    assert!(env.has_add_semigroup());
    assert!(env.has_monoid());
    assert!(env.has_add_monoid());
    assert!(env.has_nat_add_semigroup_inst());
    assert!(env.has_int_add_semigroup_inst());
    assert!(env.has_nat_add_monoid_inst());
    assert!(env.has_int_add_monoid_inst());
}

// ========================================================================
// Tests for Group/AddGroup Typeclasses
// ========================================================================

#[test]
fn test_group_init() {
    let mut env = Environment::new();
    assert!(!env.has_group());

    env.init_group().unwrap();
    assert!(env.has_group());

    // Verify Group type exists
    assert_ind(&env, "Group");
    for s in ["Group.mk", "Group.mul", "Group.one", "Group.inv"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_add_group_init() {
    let mut env = Environment::new();
    assert!(!env.has_add_group());

    env.init_add_group().unwrap();
    assert!(env.has_add_group());

    // Verify AddGroup type exists
    assert_ind(&env, "AddGroup");
    for s in [
        "AddGroup.mk",
        "AddGroup.add",
        "AddGroup.zero",
        "AddGroup.neg",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_group_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_group().unwrap();

    let tc = TypeChecker::new(&env);

    // Check Group.mk type
    let mk = env.get_const(&Name::from_string("Group.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 8, "Group", "Group.mk");

    // Check projections
    let mul_proj = env.get_const(&Name::from_string("Group.mul")).unwrap();
    assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "Group.mul");

    let one_proj = env.get_const(&Name::from_string("Group.one")).unwrap();
    assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "Group.one");

    let inv_proj = env.get_const(&Name::from_string("Group.inv")).unwrap();
    assert_typeclass_projection_shape(&tc, &inv_proj.type_, 3, "Group.inv");
}

#[test]
fn test_add_group_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_add_group().unwrap();

    let tc = TypeChecker::new(&env);

    // Check AddGroup.mk type
    let mk = env.get_const(&Name::from_string("AddGroup.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 8, "AddGroup", "AddGroup.mk");

    // Check projections
    let add_proj = env.get_const(&Name::from_string("AddGroup.add")).unwrap();
    assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "AddGroup.add");

    let zero_proj = env.get_const(&Name::from_string("AddGroup.zero")).unwrap();
    assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "AddGroup.zero");

    let neg_proj = env.get_const(&Name::from_string("AddGroup.neg")).unwrap();
    assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "AddGroup.neg");
}

#[test]
fn test_int_add_group_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_group_inst());

    env.init_int_add_group_inst().unwrap();
    assert!(env.has_int_add_group_inst());

    assert_const(&env, "instAddGroupInt");
}

#[test]
fn test_int_add_group_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_add_group_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instAddGroupInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "AddGroup",
        "instAddGroupInt",
    );
}

/// Verify Int.zero representation: instZeroInt should use Int.ofNat Nat.zero,
/// not some other encoding. Catches regressions where the zero representation
/// changes silently.
#[test]
fn test_int_zero_inst_representation() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_zero_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instZeroInt"))
        .expect("instZeroInt should exist");
    assert_concrete_instance_shape(&tc, &info.type_, info.value.as_ref(), "Zero", "instZeroInt");

    // The value should be `Zero.mk Int (Int.ofNat Nat.zero)`.
    // Walk the value App tree to find Int.ofNat and Nat.zero constants,
    // which confirms the representation hasn't regressed.
    let decl_value = info
        .value
        .as_ref()
        .expect("instZeroInt should be defined with a value");
    let value_consts = collect_const_names(decl_value);
    assert!(
        value_consts.contains(&"Int.ofNat".to_string()),
        "instZeroInt value should reference Int.ofNat, got: {value_consts:?}"
    );
    assert!(
        value_consts.contains(&"Nat.zero".to_string()),
        "instZeroInt value should reference Nat.zero, got: {value_consts:?}"
    );
}

/// Collect all constant names referenced in an expression tree.
fn collect_const_names(expr: &Expr) -> Vec<String> {
    use crate::expr::ExprKind;
    let mut names = Vec::new();
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        match &e.kind {
            ExprKind::Const(name, _) => names.push(name.to_string()),
            ExprKind::App(f, a) => {
                stack.push(f.as_ref());
                stack.push(a.as_ref());
            }
            ExprKind::Lam(_, d, b) | ExprKind::Pi(_, d, b) => {
                stack.push(d.as_ref());
                stack.push(b.as_ref());
            }
            ExprKind::Let(_, t, v, b, _) => {
                stack.push(t.as_ref());
                stack.push(v.as_ref());
                stack.push(b.as_ref());
            }
            _ => {}
        }
    }
    names
}

#[test]
fn test_group_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_group().unwrap();
    env.init_group().unwrap();
    env.init_add_group().unwrap();
    env.init_add_group().unwrap();
    env.init_int_add_group_inst().unwrap();
    env.init_int_add_group_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_group());
    assert!(env.has_add_group());
    assert!(env.has_int_add_group_inst());
}

// Tests for Commutative Algebraic Structure Typeclasses

#[test]
fn test_comm_semigroup_init() {
    let mut env = Environment::new();
    assert!(!env.has_comm_semigroup());

    env.init_comm_semigroup().unwrap();
    assert!(env.has_comm_semigroup());

    // Verify CommSemigroup type exists
    assert!(env
        .get_inductive(&Name::from_string("CommSemigroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("CommSemigroup.mk"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("CommSemigroup.mul"))
        .is_some());
}

#[test]
fn test_add_comm_semigroup_init() {
    let mut env = Environment::new();
    assert!(!env.has_add_comm_semigroup());

    env.init_add_comm_semigroup().unwrap();
    assert!(env.has_add_comm_semigroup());

    // Verify AddCommSemigroup type exists
    assert!(env
        .get_inductive(&Name::from_string("AddCommSemigroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AddCommSemigroup.mk"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AddCommSemigroup.add"))
        .is_some());
}

#[test]
fn test_comm_monoid_init() {
    let mut env = Environment::new();
    assert!(!env.has_comm_monoid());

    env.init_comm_monoid().unwrap();
    assert!(env.has_comm_monoid());

    // Verify CommMonoid type exists
    assert_ind(&env, "CommMonoid");
    for s in ["CommMonoid.mk", "CommMonoid.mul", "CommMonoid.one"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_add_comm_monoid_init() {
    let mut env = Environment::new();
    assert!(!env.has_add_comm_monoid());

    env.init_add_comm_monoid().unwrap();
    assert!(env.has_add_comm_monoid());

    // Verify AddCommMonoid type exists
    assert_ind(&env, "AddCommMonoid");
    for s in [
        "AddCommMonoid.mk",
        "AddCommMonoid.add",
        "AddCommMonoid.zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_comm_group_init() {
    let mut env = Environment::new();
    assert!(!env.has_comm_group());

    env.init_comm_group().unwrap();
    assert!(env.has_comm_group());

    // Verify CommGroup type exists
    assert_ind(&env, "CommGroup");
    for s in [
        "CommGroup.mk",
        "CommGroup.mul",
        "CommGroup.one",
        "CommGroup.inv",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_add_comm_group_init() {
    let mut env = Environment::new();
    assert!(!env.has_add_comm_group());

    env.init_add_comm_group().unwrap();
    assert!(env.has_add_comm_group());

    // Verify AddCommGroup type exists
    assert!(env
        .get_inductive(&Name::from_string("AddCommGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AddCommGroup.mk"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AddCommGroup.add"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AddCommGroup.zero"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AddCommGroup.neg"))
        .is_some());
}

#[test]
fn test_comm_semigroup_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_comm_semigroup().unwrap();

    let tc = TypeChecker::new(&env);

    // Check CommSemigroup.mk type
    let mk = env
        .get_const(&Name::from_string("CommSemigroup.mk"))
        .unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 4, "CommSemigroup", "CommSemigroup.mk");

    // Check projections
    let mul_proj = env
        .get_const(&Name::from_string("CommSemigroup.mul"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "CommSemigroup.mul");
}

#[test]
fn test_add_comm_semigroup_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_add_comm_semigroup().unwrap();

    let tc = TypeChecker::new(&env);

    // Check AddCommSemigroup.mk type
    let mk = env
        .get_const(&Name::from_string("AddCommSemigroup.mk"))
        .unwrap();
    assert_typeclass_constructor_shape(
        &tc,
        &mk.type_,
        4,
        "AddCommSemigroup",
        "AddCommSemigroup.mk",
    );

    // Check projections
    let add_proj = env
        .get_const(&Name::from_string("AddCommSemigroup.add"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "AddCommSemigroup.add");
}

#[test]
fn test_comm_monoid_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_comm_monoid().unwrap();

    let tc = TypeChecker::new(&env);

    // Check CommMonoid.mk type
    let mk = env.get_const(&Name::from_string("CommMonoid.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 7, "CommMonoid", "CommMonoid.mk");

    // Check projections
    let mul_proj = env.get_const(&Name::from_string("CommMonoid.mul")).unwrap();
    assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "CommMonoid.mul");

    let one_proj = env.get_const(&Name::from_string("CommMonoid.one")).unwrap();
    assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "CommMonoid.one");
}

#[test]
fn test_add_comm_monoid_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_add_comm_monoid().unwrap();

    let tc = TypeChecker::new(&env);

    // Check AddCommMonoid.mk type
    let mk = env
        .get_const(&Name::from_string("AddCommMonoid.mk"))
        .unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 7, "AddCommMonoid", "AddCommMonoid.mk");

    // Check projections
    let add_proj = env
        .get_const(&Name::from_string("AddCommMonoid.add"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "AddCommMonoid.add");

    let zero_proj = env
        .get_const(&Name::from_string("AddCommMonoid.zero"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "AddCommMonoid.zero");
}

#[test]
fn test_comm_group_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_comm_group().unwrap();

    let tc = TypeChecker::new(&env);

    // Check CommGroup.mk type
    let mk = env.get_const(&Name::from_string("CommGroup.mk")).unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 9, "CommGroup", "CommGroup.mk");

    // Check projections
    let mul_proj = env.get_const(&Name::from_string("CommGroup.mul")).unwrap();
    assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "CommGroup.mul");

    let one_proj = env.get_const(&Name::from_string("CommGroup.one")).unwrap();
    assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "CommGroup.one");

    let inv_proj = env.get_const(&Name::from_string("CommGroup.inv")).unwrap();
    assert_typeclass_projection_shape(&tc, &inv_proj.type_, 3, "CommGroup.inv");
}

#[test]
fn test_add_comm_group_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_add_comm_group().unwrap();

    let tc = TypeChecker::new(&env);

    // Check AddCommGroup.mk type
    let mk = env
        .get_const(&Name::from_string("AddCommGroup.mk"))
        .unwrap();
    assert_typeclass_constructor_shape(&tc, &mk.type_, 9, "AddCommGroup", "AddCommGroup.mk");

    // Check projections
    let add_proj = env
        .get_const(&Name::from_string("AddCommGroup.add"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "AddCommGroup.add");

    let zero_proj = env
        .get_const(&Name::from_string("AddCommGroup.zero"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "AddCommGroup.zero");

    let neg_proj = env
        .get_const(&Name::from_string("AddCommGroup.neg"))
        .unwrap();
    assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "AddCommGroup.neg");
}

#[test]
fn test_nat_add_comm_semigroup_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_add_comm_semigroup_inst());

    env.init_nat_add_comm_semigroup_inst().unwrap();
    assert!(env.has_nat_add_comm_semigroup_inst());

    assert!(env
        .get_const(&Name::from_string("instAddCommSemigroupNat"))
        .is_some());
}

#[test]
fn test_int_add_comm_semigroup_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_comm_semigroup_inst());

    env.init_int_add_comm_semigroup_inst().unwrap();
    assert!(env.has_int_add_comm_semigroup_inst());

    assert!(env
        .get_const(&Name::from_string("instAddCommSemigroupInt"))
        .is_some());
}

#[test]
fn test_nat_add_comm_monoid_inst() {
    let mut env = Environment::new();
    assert!(!env.has_nat_add_comm_monoid_inst());

    env.init_nat_add_comm_monoid_inst().unwrap();
    assert!(env.has_nat_add_comm_monoid_inst());

    assert!(env
        .get_const(&Name::from_string("instAddCommMonoidNat"))
        .is_some());
}

#[test]
fn test_int_add_comm_monoid_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_comm_monoid_inst());

    env.init_int_add_comm_monoid_inst().unwrap();
    assert!(env.has_int_add_comm_monoid_inst());

    assert!(env
        .get_const(&Name::from_string("instAddCommMonoidInt"))
        .is_some());
}

#[test]
fn test_int_add_comm_group_inst() {
    let mut env = Environment::new();
    assert!(!env.has_int_add_comm_group_inst());

    env.init_int_add_comm_group_inst().unwrap();
    assert!(env.has_int_add_comm_group_inst());

    assert!(env
        .get_const(&Name::from_string("instAddCommGroupInt"))
        .is_some());
}

#[test]
fn test_nat_add_comm_semigroup_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_comm_semigroup_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instAddCommSemigroupNat"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "AddCommSemigroup",
        "instAddCommSemigroupNat",
    );
}

#[test]
fn test_int_add_comm_semigroup_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_add_comm_semigroup_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instAddCommSemigroupInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "AddCommSemigroup",
        "instAddCommSemigroupInt",
    );
}

#[test]
fn test_nat_add_comm_monoid_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_add_comm_monoid_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instAddCommMonoidNat"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "AddCommMonoid",
        "instAddCommMonoidNat",
    );
}

#[test]
fn test_int_add_comm_monoid_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_add_comm_monoid_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instAddCommMonoidInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "AddCommMonoid",
        "instAddCommMonoidInt",
    );
}

#[test]
fn test_int_add_comm_group_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_add_comm_group_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instAddCommGroupInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "AddCommGroup",
        "instAddCommGroupInt",
    );
}

#[test]
fn test_comm_typeclasses_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_comm_semigroup().unwrap();
    env.init_comm_semigroup().unwrap();
    env.init_add_comm_semigroup().unwrap();
    env.init_add_comm_semigroup().unwrap();
    env.init_comm_monoid().unwrap();
    env.init_comm_monoid().unwrap();
    env.init_add_comm_monoid().unwrap();
    env.init_add_comm_monoid().unwrap();
    env.init_comm_group().unwrap();
    env.init_comm_group().unwrap();
    env.init_add_comm_group().unwrap();
    env.init_add_comm_group().unwrap();

    // Instances
    env.init_nat_add_comm_semigroup_inst().unwrap();
    env.init_nat_add_comm_semigroup_inst().unwrap();
    env.init_int_add_comm_semigroup_inst().unwrap();
    env.init_int_add_comm_semigroup_inst().unwrap();
    env.init_nat_add_comm_monoid_inst().unwrap();
    env.init_nat_add_comm_monoid_inst().unwrap();
    env.init_int_add_comm_monoid_inst().unwrap();
    env.init_int_add_comm_monoid_inst().unwrap();
    env.init_int_add_comm_group_inst().unwrap();
    env.init_int_add_comm_group_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_comm_semigroup());
    assert!(env.has_add_comm_semigroup());
    assert!(env.has_comm_monoid());
    assert!(env.has_add_comm_monoid());
    assert!(env.has_comm_group());
    assert!(env.has_add_comm_group());
    assert!(env.has_nat_add_comm_semigroup_inst());
    assert!(env.has_int_add_comm_semigroup_inst());
    assert!(env.has_nat_add_comm_monoid_inst());
    assert!(env.has_int_add_comm_monoid_inst());
    assert!(env.has_int_add_comm_group_inst());
}

#[test]
fn test_semiring_init() {
    let mut env = Environment::new();
    assert!(!env.has_semiring());

    env.init_semiring().unwrap();
    assert!(env.has_semiring());

    // Verify Semiring type exists
    assert_ind(&env, "Semiring");
    for s in [
        "Semiring.mk",
        "Semiring.add",
        "Semiring.zero",
        "Semiring.mul",
        "Semiring.one",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_ring_init() {
    let mut env = Environment::new();
    assert!(!env.has_ring());

    env.init_ring().unwrap();
    assert!(env.has_ring());

    // Verify Ring type exists
    assert_ind(&env, "Ring");
    for s in [
        "Ring.mk",
        "Ring.add",
        "Ring.zero",
        "Ring.mul",
        "Ring.one",
        "Ring.neg",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_semiring_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_semiring().unwrap();

        let tc = TypeChecker::new(&env);

        let mk = env.get_const(&Name::from_string("Semiring.mk")).unwrap();
        assert_typeclass_constructor_shape(&tc, &mk.type_, 16, "Semiring", "Semiring.mk");

        let add_proj = env.get_const(&Name::from_string("Semiring.add")).unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "Semiring.add");

        let zero_proj = env.get_const(&Name::from_string("Semiring.zero")).unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "Semiring.zero");

        let mul_proj = env.get_const(&Name::from_string("Semiring.mul")).unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "Semiring.mul");

        let one_proj = env.get_const(&Name::from_string("Semiring.one")).unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "Semiring.one");
    });
}

#[test]
fn test_ring_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_ring().unwrap();

        let tc = TypeChecker::new(&env);

        let mk = env.get_const(&Name::from_string("Ring.mk")).unwrap();
        assert_typeclass_constructor_shape(&tc, &mk.type_, 18, "Ring", "Ring.mk");

        let add_proj = env.get_const(&Name::from_string("Ring.add")).unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "Ring.add");

        let zero_proj = env.get_const(&Name::from_string("Ring.zero")).unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "Ring.zero");

        let mul_proj = env.get_const(&Name::from_string("Ring.mul")).unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "Ring.mul");

        let one_proj = env.get_const(&Name::from_string("Ring.one")).unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "Ring.one");

        let neg_proj = env.get_const(&Name::from_string("Ring.neg")).unwrap();
        assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "Ring.neg");
    });
}

/// Count Pi binders in a type expression, returning (count, codomain after all binders).
fn count_pi_binders(expr: &Expr) -> (usize, Expr) {
    let mut count = 0;
    let mut current = expr.clone();
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count += 1;
        current = body.as_ref().clone();
    }
    (count, current)
}

#[test]
fn test_nat_semiring_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_nat_semiring_inst());

    env.init_nat_semiring_inst().unwrap();
    assert!(env.has_nat_semiring_inst());

    // Verify instance exists
    assert!(env
        .get_const(&Name::from_string("instSemiringNat"))
        .is_some());
}

#[test]
fn test_int_semiring_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_semiring_inst());

    env.init_int_semiring_inst().unwrap();
    assert!(env.has_int_semiring_inst());

    // Verify instance exists
    assert_const(&env, "instSemiringInt");
}

#[test]
fn test_int_ring_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_ring_inst());

    env.init_int_ring_inst().unwrap();
    assert!(env.has_int_ring_inst());

    // Verify instance exists
    assert_const(&env, "instRingInt");
}

#[test]
fn test_nat_semiring_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_semiring_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instSemiringNat"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "Semiring",
        "instSemiringNat",
    );
}

#[test]
fn test_int_semiring_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_semiring_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instSemiringInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "Semiring",
        "instSemiringInt",
    );
}

#[test]
fn test_int_ring_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_ring_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env.get_const(&Name::from_string("instRingInt")).unwrap();
    assert_concrete_instance_shape(&tc, &info.type_, info.value.as_ref(), "Ring", "instRingInt");
}

#[test]
fn test_semiring_ring_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_semiring().unwrap();
    env.init_semiring().unwrap();
    env.init_ring().unwrap();
    env.init_ring().unwrap();

    // Instances
    env.init_nat_semiring_inst().unwrap();
    env.init_nat_semiring_inst().unwrap();
    env.init_int_semiring_inst().unwrap();
    env.init_int_semiring_inst().unwrap();
    env.init_int_ring_inst().unwrap();
    env.init_int_ring_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_semiring());
    assert!(env.has_ring());
    assert!(env.has_nat_semiring_inst());
    assert!(env.has_int_semiring_inst());
    assert!(env.has_int_ring_inst());
}

#[test]
fn test_comm_semiring_init() {
    let mut env = Environment::new();
    assert!(!env.has_comm_semiring());

    env.init_comm_semiring().unwrap();
    assert!(env.has_comm_semiring());

    // Verify CommSemiring type exists
    assert_ind(&env, "CommSemiring");
    for s in [
        "CommSemiring.mk",
        "CommSemiring.add",
        "CommSemiring.zero",
        "CommSemiring.mul",
        "CommSemiring.one",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_comm_ring_init() {
    let mut env = Environment::new();
    assert!(!env.has_comm_ring());

    env.init_comm_ring().unwrap();
    assert!(env.has_comm_ring());

    // Verify CommRing type exists
    assert_ind(&env, "CommRing");
    for s in [
        "CommRing.mk",
        "CommRing.add",
        "CommRing.zero",
        "CommRing.mul",
        "CommRing.one",
        "CommRing.neg",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_comm_semiring_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_comm_semiring().unwrap();

        let tc = TypeChecker::new(&env);

        let mk = env
            .get_const(&Name::from_string("CommSemiring.mk"))
            .unwrap();
        assert_typeclass_constructor_shape(&tc, &mk.type_, 17, "CommSemiring", "CommSemiring.mk");

        let add_proj = env
            .get_const(&Name::from_string("CommSemiring.add"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "CommSemiring.add");

        let zero_proj = env
            .get_const(&Name::from_string("CommSemiring.zero"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "CommSemiring.zero");

        let mul_proj = env
            .get_const(&Name::from_string("CommSemiring.mul"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "CommSemiring.mul");

        let one_proj = env
            .get_const(&Name::from_string("CommSemiring.one"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "CommSemiring.one");
    });
}

#[test]
fn test_comm_ring_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_comm_ring().unwrap();

        let tc = TypeChecker::new(&env);

        let mk = env.get_const(&Name::from_string("CommRing.mk")).unwrap();
        assert_typeclass_constructor_shape(&tc, &mk.type_, 19, "CommRing", "CommRing.mk");

        let add_proj = env.get_const(&Name::from_string("CommRing.add")).unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "CommRing.add");

        let zero_proj = env.get_const(&Name::from_string("CommRing.zero")).unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "CommRing.zero");

        let mul_proj = env.get_const(&Name::from_string("CommRing.mul")).unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "CommRing.mul");

        let one_proj = env.get_const(&Name::from_string("CommRing.one")).unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "CommRing.one");

        let neg_proj = env.get_const(&Name::from_string("CommRing.neg")).unwrap();
        assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "CommRing.neg");
    });
}

/// Test CommRing.toRing inheritance projection (#143).
///
/// This test verifies the de Bruijn indices in the CommRing.toRing motive.
/// The motive is: λ (x : CommRing α) => Ring α
///
/// Correct indices (standalone pattern):
/// - Binder type: CommRing bvar(0) -- α is free variable at depth 0
/// - Body: Ring bvar(1) -- α shifts by 1 due to the lambda binder
///
/// Bug (P114): Using bvar(1)/bvar(2) instead of bvar(0)/bvar(1)
/// causes type checking to fail because α references non-existent binders.
#[test]
fn test_issue143_commring_to_ring_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_comm_ring().unwrap();

        let tc = TypeChecker::new(&env);

        // CommRing.toRing must exist
        let to_ring = env
            .get_const(&Name::from_string("CommRing.toRing"))
            .expect("CommRing.toRing should be defined by init_comm_ring()");

        // Type: {α : Type u} → [CommRing α] → Ring α
        // This type check will fail if the motive has wrong de Bruijn indices
        let _ = tc
            .infer_type(&to_ring.type_)
            .expect("CommRing.toRing type should type-check");

        // Value type check - this is where the de Bruijn bug manifests
        let _ = tc
            .infer_type(&to_ring.value.clone().expect("should have value"))
            .expect("CommRing.toRing value should type-check");

        // Verify the value has the correct type
        let inferred = tc
            .infer_type(&to_ring.value.clone().expect("should have value"))
            .unwrap();
        let expected = to_ring.type_.clone();

        // The inferred type should be definitionally equal to the declared type
        assert!(
            tc.is_def_eq(&inferred, &expected),
            "CommRing.toRing value type mismatch: inferred {:?}, expected {:?}",
            inferred,
            expected
        );
    });
}

#[test]
fn test_nat_comm_semiring_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_nat_comm_semiring_inst());

    env.init_nat_comm_semiring_inst().unwrap();
    assert!(env.has_nat_comm_semiring_inst());

    // Verify instance exists
    assert!(env
        .get_const(&Name::from_string("instCommSemiringNat"))
        .is_some());
}

#[test]
fn test_int_comm_semiring_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_comm_semiring_inst());

    env.init_int_comm_semiring_inst().unwrap();
    assert!(env.has_int_comm_semiring_inst());

    // Verify instance exists
    assert!(env
        .get_const(&Name::from_string("instCommSemiringInt"))
        .is_some());
}

#[test]
fn test_int_comm_ring_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_comm_ring_inst());

    env.init_int_comm_ring_inst().unwrap();
    assert!(env.has_int_comm_ring_inst());

    // Verify instance exists
    assert!(env
        .get_const(&Name::from_string("instCommRingInt"))
        .is_some());
}

#[test]
fn test_nat_comm_semiring_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_nat_comm_semiring_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instCommSemiringNat"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "CommSemiring",
        "instCommSemiringNat",
    );
}

#[test]
fn test_int_comm_semiring_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_comm_semiring_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instCommSemiringInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "CommSemiring",
        "instCommSemiringInt",
    );
}

#[test]
fn test_int_comm_ring_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_comm_ring_inst().unwrap();

    let tc = TypeChecker::new(&env);

    let info = env
        .get_const(&Name::from_string("instCommRingInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &info.type_,
        info.value.as_ref(),
        "CommRing",
        "instCommRingInt",
    );
}

#[test]
fn test_comm_semiring_comm_ring_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_comm_semiring().unwrap();
    env.init_comm_semiring().unwrap();
    env.init_comm_ring().unwrap();
    env.init_comm_ring().unwrap();

    // Instances
    env.init_nat_comm_semiring_inst().unwrap();
    env.init_nat_comm_semiring_inst().unwrap();
    env.init_int_comm_semiring_inst().unwrap();
    env.init_int_comm_semiring_inst().unwrap();
    env.init_int_comm_ring_inst().unwrap();
    env.init_int_comm_ring_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_comm_semiring());
    assert!(env.has_comm_ring());
    assert!(env.has_nat_comm_semiring_inst());
    assert!(env.has_int_comm_semiring_inst());
    assert!(env.has_int_comm_ring_inst());
}

// ===== DivisionRing and Field Tests =====

#[test]
fn test_ne_definition() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_true_false().unwrap();

    // Verify Ne exists
    let ne = env.get_const(&Name::from_string("Ne")).unwrap();
    let ne_value = ne.value.as_ref().expect("Ne should have a definition body");
    // Ne's value should be a lambda (fun a b => Not (a = b))
    assert!(
        matches!(&ne_value.kind, ExprKind::Lam(..)),
        "Ne value should be a lambda, got {:?}",
        ne_value.kind
    );

    // Type check Ne
    let tc = TypeChecker::new(&env);
    let ne_ty = tc.infer_type(&ne.type_).unwrap();
    assert!(
        matches!(&ne_ty.kind, ExprKind::Sort(..)),
        "type of Ne's type should be Sort, got {:?}",
        ne_ty.kind
    );
}

#[test]
fn test_division_ring_init() {
    let mut env = Environment::new();
    assert!(!env.has_division_ring());

    env.init_division_ring().unwrap();
    assert!(env.has_division_ring());

    // Verify DivisionRing, constructor, and projections exist
    for s in [
        "DivisionRing",
        "DivisionRing.mk",
        "DivisionRing.rec",
        "DivisionRing.add",
        "DivisionRing.zero",
        "DivisionRing.mul",
        "DivisionRing.one",
        "DivisionRing.neg",
        "DivisionRing.inv",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_division_ring_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_division_ring().unwrap();

        let tc = TypeChecker::new(&env);

        let mk = env
            .get_const(&Name::from_string("DivisionRing.mk"))
            .unwrap();
        assert_typeclass_constructor_shape(&tc, &mk.type_, 21, "DivisionRing", "DivisionRing.mk");

        let add_proj = env
            .get_const(&Name::from_string("DivisionRing.add"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "DivisionRing.add");

        let zero_proj = env
            .get_const(&Name::from_string("DivisionRing.zero"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "DivisionRing.zero");

        let mul_proj = env
            .get_const(&Name::from_string("DivisionRing.mul"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "DivisionRing.mul");

        let one_proj = env
            .get_const(&Name::from_string("DivisionRing.one"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "DivisionRing.one");

        let neg_proj = env
            .get_const(&Name::from_string("DivisionRing.neg"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "DivisionRing.neg");

        let inv_proj = env
            .get_const(&Name::from_string("DivisionRing.inv"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &inv_proj.type_, 3, "DivisionRing.inv");
    });
}

#[test]
fn test_field_init() {
    let mut env = Environment::new();
    assert!(!env.has_field());

    env.init_field().unwrap();
    assert!(env.has_field());

    // Verify Field, constructor, and projections exist
    for s in [
        "Field",
        "Field.mk",
        "Field.rec",
        "Field.add",
        "Field.zero",
        "Field.mul",
        "Field.one",
        "Field.neg",
        "Field.inv",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_field_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_field().unwrap();

        let tc = TypeChecker::new(&env);

        let mk = env.get_const(&Name::from_string("Field.mk")).unwrap();
        assert_typeclass_constructor_shape(&tc, &mk.type_, 22, "Field", "Field.mk");

        let add_proj = env.get_const(&Name::from_string("Field.add")).unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "Field.add");

        let zero_proj = env.get_const(&Name::from_string("Field.zero")).unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "Field.zero");

        let mul_proj = env.get_const(&Name::from_string("Field.mul")).unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "Field.mul");

        let one_proj = env.get_const(&Name::from_string("Field.one")).unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "Field.one");

        let neg_proj = env.get_const(&Name::from_string("Field.neg")).unwrap();
        assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "Field.neg");

        let inv_proj = env.get_const(&Name::from_string("Field.inv")).unwrap();
        assert_typeclass_projection_shape(&tc, &inv_proj.type_, 3, "Field.inv");
    });
}

#[test]
fn test_division_ring_field_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_division_ring().unwrap();
    env.init_division_ring().unwrap();
    env.init_field().unwrap();
    env.init_field().unwrap();

    // Verify all flags are set
    assert!(env.has_division_ring());
    assert!(env.has_field());
}

#[test]
fn test_integral_domain_init() {
    let mut env = Environment::new();
    env.init_integral_domain().unwrap();

    // Verify IntegralDomain is registered
    assert!(env
        .get_inductive(&Name::from_string("IntegralDomain"))
        .is_some());

    // Verify projections
    assert!(env
        .get_const(&Name::from_string("IntegralDomain.add"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("IntegralDomain.zero"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("IntegralDomain.mul"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("IntegralDomain.one"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("IntegralDomain.neg"))
        .is_some());

    // Verify flag
    assert!(env.has_integral_domain());
}

#[test]
fn test_integral_domain_type_check() {
    with_large_stack(|| {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_integral_domain().unwrap();

        let tc = TypeChecker::new(&env);

        let ind = env
            .get_inductive(&Name::from_string("IntegralDomain"))
            .unwrap();
        let ind_type_of_type = tc
            .infer_type(&ind.type_)
            .unwrap_or_else(|e| panic!("IntegralDomain type should be well-formed: {e:?}"));
        assert!(
            matches!(&ind_type_of_type.kind, ExprKind::Sort(_)),
            "IntegralDomain type should infer to a sort, got {ind_type_of_type:?}"
        );
        let (ind_binders, ind_codomain) = count_pi_binders(&ind.type_);
        assert_eq!(
            ind_binders, 1,
            "IntegralDomain should quantify exactly one carrier type"
        );
        assert!(
            matches!(&ind_codomain.kind, ExprKind::Sort(_)),
            "IntegralDomain codomain should be a sort, got {ind_codomain:?}"
        );

        let ctor = env
            .get_constructor(&Name::from_string("IntegralDomain.mk"))
            .unwrap();
        assert_typeclass_constructor_shape(
            &tc,
            &ctor.type_,
            20,
            "IntegralDomain",
            "IntegralDomain.mk",
        );

        let add_proj = env
            .get_const(&Name::from_string("IntegralDomain.add"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &add_proj.type_, 4, "IntegralDomain.add");

        let zero_proj = env
            .get_const(&Name::from_string("IntegralDomain.zero"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &zero_proj.type_, 2, "IntegralDomain.zero");

        let mul_proj = env
            .get_const(&Name::from_string("IntegralDomain.mul"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &mul_proj.type_, 4, "IntegralDomain.mul");

        let one_proj = env
            .get_const(&Name::from_string("IntegralDomain.one"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &one_proj.type_, 2, "IntegralDomain.one");

        let neg_proj = env
            .get_const(&Name::from_string("IntegralDomain.neg"))
            .unwrap();
        assert_typeclass_projection_shape(&tc, &neg_proj.type_, 3, "IntegralDomain.neg");
    });
}

#[test]
fn test_int_integral_domain_inst_init() {
    let mut env = Environment::new();
    env.init_int_integral_domain_inst().unwrap();

    // Verify instance is registered
    assert!(env
        .get_const(&Name::from_string("instIntegralDomainInt"))
        .is_some());

    // Verify no_zero_divisors axiom exists
    assert!(env
        .get_const(&Name::from_string("Int.no_zero_divisors"))
        .is_some());

    // Verify flag
    assert!(env.has_int_integral_domain_inst());
}

#[test]
fn test_int_integral_domain_inst_type_check() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_int_integral_domain_inst().unwrap();

    let tc = TypeChecker::new(&env);

    // Type check the instance
    let inst = env
        .get_const(&Name::from_string("instIntegralDomainInt"))
        .unwrap();
    assert_concrete_instance_shape(
        &tc,
        &inst.type_,
        inst.value.as_ref(),
        "IntegralDomain",
        "instIntegralDomainInt",
    );
}

#[test]
fn test_integral_domain_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_integral_domain().unwrap();
    env.init_integral_domain().unwrap();
    env.init_int_integral_domain_inst().unwrap();
    env.init_int_integral_domain_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_integral_domain());
    assert!(env.has_int_integral_domain_inst());
}

#[test]
fn test_nontrivial_init() {
    let mut env = Environment::new();
    assert!(!env.has_nontrivial());

    env.init_nontrivial().unwrap();
    assert!(env.has_nontrivial());

    // Verify the Nontrivial type is registered
    assert_const(&env, "Nontrivial");
    let mk_n = Name::from_string("Nontrivial.mk");
    let mk_ctor = env.get_constructor(&mk_n).expect("Nontrivial.mk");
    assert_eq!(mk_ctor.name, mk_n, "name mismatch for Nontrivial.mk");
    let rec_n = Name::from_string("Nontrivial.rec");
    let rec_info = env.get_recursor(&rec_n).expect("Nontrivial.rec");
    assert_eq!(rec_info.name, rec_n, "name mismatch for Nontrivial.rec");
    assert_const(&env, "Nontrivial.exists_pair_ne");
}

#[test]
fn test_nontrivial_type_check() {
    let mut env = Environment::new();
    env.init_nontrivial().unwrap();

    // Check Nontrivial : Type u → Prop  (Type u = Sort (u+1))
    let nontrivial_info = env.get_const(&Name::from_string("Nontrivial")).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(
            Name::from_string("u"),
        )))),
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );
    assert_eq!(
        nontrivial_info.type_, expected_type,
        "Nontrivial should have type: Type u → Prop"
    );
}

#[test]
fn test_int_nontrivial_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_nontrivial_inst());

    env.init_int_nontrivial_inst().unwrap();
    assert!(env.has_int_nontrivial_inst());

    // Verify the instance is registered
    assert!(env
        .get_const(&Name::from_string("instNontrivialInt"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Int.zero_ne_one"))
        .is_some());
}

#[test]
fn test_int_nontrivial_inst_type_check() {
    let mut env = Environment::new();
    env.init_int_nontrivial_inst().unwrap();

    // Check instNontrivialInt : Nontrivial.{0} Int
    // Nontrivial.{u} takes Type u = Sort (u+1). Int : Type = Sort 1, so u = 0.
    let inst_info = env
        .get_const(&Name::from_string("instNontrivialInt"))
        .unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("Nontrivial"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Int"), vec![]),
    );
    assert_eq!(
        inst_info.type_, expected_type,
        "instNontrivialInt should have type: Nontrivial.{{0}} Int"
    );
}

#[test]
fn test_well_founded_init() {
    let mut env = Environment::new();
    assert!(!env.has_well_founded());

    env.init_well_founded().unwrap();
    assert!(env.has_well_founded());

    // Verify Acc is registered
    assert_const(&env, "Acc");
    let acc_intro = Name::from_string("Acc.intro");
    assert_eq!(
        env.get_constructor(&acc_intro).expect("Acc.intro").name,
        acc_intro
    );
    let acc_rec = Name::from_string("Acc.rec");
    let acc_rec_val = env.get_recursor(&acc_rec).expect("Acc.rec");
    assert_eq!(acc_rec_val.name, acc_rec);
    // #2437: Acc.rec must have 2 universe level params [motive_u, u],
    // not 1 — the old infer_sort_level returned None for App expressions,
    // causing elim_only_at_universe_zero to incorrectly restrict Acc to
    // Prop-only elimination (1 param instead of 2).
    assert_eq!(
        acc_rec_val.level_params.len(),
        2,
        "Acc.rec should have 2 universe level params [motive_u, u], not 1"
    );

    // Verify WellFounded is registered
    assert_const(&env, "WellFounded");
    let wf_intro = Name::from_string("WellFounded.intro");
    assert_eq!(
        env.get_constructor(&wf_intro)
            .expect("WellFounded.intro")
            .name,
        wf_intro
    );
    let wf_rec = Name::from_string("WellFounded.rec");
    assert_eq!(
        env.get_recursor(&wf_rec).expect("WellFounded.rec").name,
        wf_rec
    );

    // Verify WellFounded.fixF is registered (added for #1132)
    let fix_f = Name::from_string("WellFounded.fixF");
    assert!(
        env.get_const(&fix_f).is_some(),
        "WellFounded.fixF should be registered"
    );

    // Verify WellFounded.fix is registered (added for #1132)
    let fix = Name::from_string("WellFounded.fix");
    assert!(
        env.get_const(&fix).is_some(),
        "WellFounded.fix should be registered"
    );
}

#[test]
fn test_well_founded_type_check() {
    let mut env = Environment::new();
    env.init_well_founded().unwrap();

    // Check Acc : {α : Sort u} → (α → α → Prop) → α → Prop
    let acc_info = env.get_const(&Name::from_string("Acc")).unwrap();
    assert_eq!(acc_info.level_params.len(), 1);

    // Check WellFounded : {α : Sort u} → (α → α → Prop) → Prop
    let wf_info = env.get_const(&Name::from_string("WellFounded")).unwrap();
    assert_eq!(wf_info.level_params.len(), 1);

    // WellFounded.fixF and WellFounded.fix have 2 level params [u, v]
    let fix_f_info = env
        .get_const(&Name::from_string("WellFounded.fixF"))
        .unwrap();
    assert_eq!(
        fix_f_info.level_params.len(),
        2,
        "fixF should have 2 universe params [u, v]"
    );

    let fix_info = env
        .get_const(&Name::from_string("WellFounded.fix"))
        .unwrap();
    assert_eq!(
        fix_info.level_params.len(),
        2,
        "fix should have 2 universe params [u, v]"
    );
}

/// Verify that WellFounded.fixF and WellFounded.fix type-check via add_decl.
///
/// Since init_well_founded() uses add_decl (not add_decl_unchecked), the kernel
/// type-checker validates both the type and value of each definition. If this
/// test passes, the fixF and fix expressions are well-typed.
#[test]
fn test_well_founded_fix_type_checked_by_add_decl() {
    let mut env = Environment::new();
    // init_well_founded uses add_decl which runs the type checker.
    // If fixF or fix have type errors, this panics.
    env.init_well_founded().unwrap();

    // Double-check: fixF value should be a lambda (fun {α} {r} {C} F x a => ...)
    let fix_f_info = env
        .get_const(&Name::from_string("WellFounded.fixF"))
        .unwrap();
    assert!(
        fix_f_info.value.is_some(),
        "fixF should be a definition with a value"
    );

    let fix_info = env
        .get_const(&Name::from_string("WellFounded.fix"))
        .unwrap();
    assert!(
        fix_info.value.is_some(),
        "fix should be a definition with a value"
    );
}

#[test]
fn test_euclidean_domain_init() {
    let mut env = Environment::new();
    assert!(!env.has_euclidean_domain());

    env.init_euclidean_domain().unwrap();
    assert!(env.has_euclidean_domain());

    // Verify the EuclideanDomain type is registered
    assert!(env
        .get_const(&Name::from_string("EuclideanDomain"))
        .is_some());
    assert!(env
        .get_constructor(&Name::from_string("EuclideanDomain.mk"))
        .is_some());
    assert!(env
        .get_recursor(&Name::from_string("EuclideanDomain.rec"))
        .is_some());

    // Verify projections are registered
    assert!(env
        .get_const(&Name::from_string("EuclideanDomain.quotient"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("EuclideanDomain.remainder"))
        .is_some());
}

#[test]
fn test_euclidean_domain_type_check() {
    let mut env = Environment::new();
    env.init_euclidean_domain().unwrap();

    // Check EuclideanDomain : Type u → Type u  (Type u = Sort (u+1))
    let ed_info = env
        .get_const(&Name::from_string("EuclideanDomain"))
        .unwrap();
    let u_level = Level::param(Name::from_string("u"));
    let expected_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
    );
    assert_eq!(
        ed_info.type_, expected_type,
        "EuclideanDomain should have type: Type u → Type u"
    );
}

#[test]
fn test_int_euclidean_domain_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_euclidean_domain_inst());

    env.init_int_euclidean_domain_inst().unwrap();
    assert!(env.has_int_euclidean_domain_inst());

    // Verify all related axioms and definitions are registered
    for s in [
        "instEuclideanDomainInt",
        "Int.div",
        "Int.mod",
        "Int.div_zero",
        "Int.div_add_mod",
        "Int.natAbs",
        "Int.euclideanLt",
        "Int.euclideanLt_wf",
        "Int.mod_lt",
        "Int.mul_not_lt",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_euclidean_domain_inst_type_check() {
    let mut env = Environment::new();
    env.init_int_euclidean_domain_inst().unwrap();

    // Check instEuclideanDomainInt : EuclideanDomain.{0} Int
    // EuclideanDomain.{u} takes Type u = Sort (u+1). Int : Type = Sort 1, so u = 0.
    let inst_info = env
        .get_const(&Name::from_string("instEuclideanDomainInt"))
        .unwrap();
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("EuclideanDomain"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Int"), vec![]),
    );
    assert_eq!(
        inst_info.type_, expected_type,
        "instEuclideanDomainInt should have type: EuclideanDomain.{{0}} Int"
    );
}

#[test]
fn test_euclidean_domain_idempotent() {
    let mut env = Environment::new();

    // Initialize all twice
    env.init_nontrivial().unwrap();
    env.init_nontrivial().unwrap();
    env.init_int_nontrivial_inst().unwrap();
    env.init_int_nontrivial_inst().unwrap();
    env.init_well_founded().unwrap();
    env.init_well_founded().unwrap();
    env.init_euclidean_domain().unwrap();
    env.init_euclidean_domain().unwrap();
    env.init_int_euclidean_domain_inst().unwrap();
    env.init_int_euclidean_domain_inst().unwrap();

    // Verify all flags are set
    assert!(env.has_nontrivial());
    assert!(env.has_int_nontrivial_inst());
    assert!(env.has_well_founded());
    assert!(env.has_euclidean_domain());
    assert!(env.has_int_euclidean_domain_inst());
}

#[test]
fn test_int_gcd_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_gcd());

    env.init_int_gcd().unwrap();
    assert!(env.has_int_gcd());

    // Verify Int.dvd, gcd, lcm, properties, and commutativity
    for s in [
        "Int.dvd",
        "Int.gcd",
        "Int.lcm",
        "Int.gcd_dvd_left",
        "Int.gcd_dvd_right",
        "Int.dvd_gcd",
        "Int.gcd_mul_lcm",
        "Int.gcd_comm",
        "Int.lcm_comm",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_gcd_type_check() {
    let mut env = Environment::new();
    env.init_int_gcd().unwrap();

    let int_type = Expr::const_(Name::from_string("Int"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Check Int.dvd : Int → Int → Prop
    let dvd_info = env.get_const(&Name::from_string("Int.dvd")).unwrap();
    let expected_dvd_type = Expr::pi(
        BinderInfo::Default,
        int_type.clone(),
        Expr::pi(BinderInfo::Default, int_type.clone(), prop),
    );
    assert_eq!(dvd_info.type_, expected_dvd_type);

    // Check Int.gcd : Int → Int → Int
    let gcd_info = env.get_const(&Name::from_string("Int.gcd")).unwrap();
    let expected_gcd_type = Expr::pi(
        BinderInfo::Default,
        int_type.clone(),
        Expr::pi(BinderInfo::Default, int_type.clone(), int_type.clone()),
    );
    assert_eq!(gcd_info.type_, expected_gcd_type);

    // Check Int.lcm : Int → Int → Int
    let lcm_info = env.get_const(&Name::from_string("Int.lcm")).unwrap();
    let expected_lcm_type = Expr::pi(
        BinderInfo::Default,
        int_type.clone(),
        Expr::pi(BinderInfo::Default, int_type.clone(), int_type),
    );
    assert_eq!(lcm_info.type_, expected_lcm_type);
}

#[test]
fn test_int_gcd_idempotent() {
    let mut env = Environment::new();

    // Initialize twice
    env.init_int_gcd().unwrap();
    env.init_int_gcd().unwrap();

    // Verify flag is set
    assert!(env.has_int_gcd());
}

#[test]
fn test_int_gcd_properties_types() {
    let mut env = Environment::new();
    env.init_int_gcd().unwrap();

    let int_type = Expr::const_(Name::from_string("Int"), vec![]);
    let int_gcd = Expr::const_(Name::from_string("Int.gcd"), vec![]);
    let int_dvd = Expr::const_(Name::from_string("Int.dvd"), vec![]);

    // Check Int.gcd_dvd_left : ∀ a b : Int, dvd (gcd a b) a
    let gcd_dvd_left_info = env
        .get_const(&Name::from_string("Int.gcd_dvd_left"))
        .unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        int_type.clone(),
        Expr::pi(BinderInfo::Default, int_type.clone(), {
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b);
            Expr::app(Expr::app(int_dvd.clone(), gcd_a_b), a)
        }),
    );
    assert_eq!(gcd_dvd_left_info.type_, expected_type);

    // Check Int.gcd_dvd_right : ∀ a b : Int, dvd (gcd a b) b
    let gcd_dvd_right_info = env
        .get_const(&Name::from_string("Int.gcd_dvd_right"))
        .unwrap();
    let expected_type2 = Expr::pi(
        BinderInfo::Default,
        int_type.clone(),
        Expr::pi(BinderInfo::Default, int_type.clone(), {
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a), b.clone());
            Expr::app(Expr::app(int_dvd, gcd_a_b), b)
        }),
    );
    assert_eq!(gcd_dvd_right_info.type_, expected_type2);
}

#[test]
fn test_int_gcd_comm_type() {
    let mut env = Environment::new();
    env.init_int_gcd().unwrap();

    let int_type = Expr::const_(Name::from_string("Int"), vec![]);
    let int_gcd = Expr::const_(Name::from_string("Int.gcd"), vec![]);

    // Check Int.gcd_comm : ∀ a b : Int, Eq (gcd a b) (gcd b a)
    let gcd_comm_info = env.get_const(&Name::from_string("Int.gcd_comm")).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        int_type.clone(),
        Expr::pi(BinderInfo::Default, int_type.clone(), {
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b.clone());
            let gcd_b_a = Expr::app(Expr::app(int_gcd, b), a);
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        int_type,
                    ),
                    gcd_a_b,
                ),
                gcd_b_a,
            )
        }),
    );
    assert_eq!(gcd_comm_info.type_, expected_type);
}

#[test]
fn test_nat_gcd_init() {
    let mut env = Environment::new();
    assert!(!env.has_nat_gcd());

    env.init_nat_gcd().unwrap();
    assert!(env.has_nat_gcd());

    // Verify Exists, Nat.dvd, gcd, lcm, properties, and divisibility
    for s in [
        "Exists", // Regression guard for #1682: Nat.dvd uses existential quantifier
        "Nat.dvd",
        "Nat.gcd",
        "Nat.lcm",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.dvd_gcd",
        "Nat.gcd_mul_lcm",
        "Nat.gcd_comm",
        "Nat.lcm_comm",
        "Nat.dvd_refl",
        "Nat.dvd_trans",
        "Nat.one_dvd",
        "Nat.dvd_zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_gcd_type_check() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Check Nat.dvd : Nat → Nat → Prop
    let dvd_info = env.get_const(&Name::from_string("Nat.dvd")).unwrap();
    let expected_dvd_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type.clone(), prop),
    );
    assert_eq!(dvd_info.type_, expected_dvd_type);

    // Check Nat.gcd : Nat → Nat → Nat
    let gcd_info = env.get_const(&Name::from_string("Nat.gcd")).unwrap();
    let expected_gcd_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type.clone(), nat_type.clone()),
    );
    assert_eq!(gcd_info.type_, expected_gcd_type);

    // Check Nat.lcm : Nat → Nat → Nat
    let lcm_info = env.get_const(&Name::from_string("Nat.lcm")).unwrap();
    let expected_lcm_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type.clone(), nat_type),
    );
    assert_eq!(lcm_info.type_, expected_lcm_type);
}

#[test]
fn test_nat_gcd_idempotent() {
    let mut env = Environment::new();

    // Initialize twice
    env.init_nat_gcd().unwrap();
    env.init_nat_gcd().unwrap();

    // Verify flag is set
    assert!(env.has_nat_gcd());
}

#[test]
fn test_nat_gcd_properties_types() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_gcd = Expr::const_(Name::from_string("Nat.gcd"), vec![]);
    let nat_dvd = Expr::const_(Name::from_string("Nat.dvd"), vec![]);

    // Check Nat.gcd_dvd_left : ∀ a b : Nat, dvd (gcd a b) a
    let gcd_dvd_left_info = env
        .get_const(&Name::from_string("Nat.gcd_dvd_left"))
        .unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type.clone(), {
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), b);
            Expr::app(Expr::app(nat_dvd.clone(), gcd_a_b), a)
        }),
    );
    assert_eq!(gcd_dvd_left_info.type_, expected_type);

    // Check Nat.gcd_dvd_right : ∀ a b : Nat, dvd (gcd a b) b
    let gcd_dvd_right_info = env
        .get_const(&Name::from_string("Nat.gcd_dvd_right"))
        .unwrap();
    let expected_type2 = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type.clone(), {
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a), b.clone());
            Expr::app(Expr::app(nat_dvd, gcd_a_b), b)
        }),
    );
    assert_eq!(gcd_dvd_right_info.type_, expected_type2);
}

#[test]
fn test_nat_gcd_comm_type() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_gcd = Expr::const_(Name::from_string("Nat.gcd"), vec![]);

    // Check Nat.gcd_comm : ∀ a b : Nat, Eq (gcd a b) (gcd b a)
    let gcd_comm_info = env.get_const(&Name::from_string("Nat.gcd_comm")).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type.clone(), {
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), b.clone());
            let gcd_b_a = Expr::app(Expr::app(nat_gcd, b), a);
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type,
                    ),
                    gcd_a_b,
                ),
                gcd_b_a,
            )
        }),
    );
    assert_eq!(gcd_comm_info.type_, expected_type);
}

#[test]
fn test_nat_dvd_properties_types() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_dvd = Expr::const_(Name::from_string("Nat.dvd"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        nat_zero.clone(),
    );

    // Check Nat.dvd_refl : ∀ a : Nat, dvd a a
    let dvd_refl_info = env.get_const(&Name::from_string("Nat.dvd_refl")).unwrap();
    let expected_refl_type = Expr::pi(BinderInfo::Default, nat_type.clone(), {
        let a = Expr::bvar(0);
        Expr::app(Expr::app(nat_dvd.clone(), a.clone()), a)
    });
    assert_eq!(dvd_refl_info.type_, expected_refl_type);

    // Check Nat.one_dvd : ∀ a : Nat, dvd 1 a
    let one_dvd_info = env.get_const(&Name::from_string("Nat.one_dvd")).unwrap();
    let expected_one_dvd_type = Expr::pi(BinderInfo::Default, nat_type.clone(), {
        let a = Expr::bvar(0);
        Expr::app(Expr::app(nat_dvd.clone(), nat_one.clone()), a)
    });
    assert_eq!(one_dvd_info.type_, expected_one_dvd_type);

    // Check Nat.dvd_zero : ∀ a : Nat, dvd a 0
    let dvd_zero_info = env.get_const(&Name::from_string("Nat.dvd_zero")).unwrap();
    let expected_dvd_zero_type = Expr::pi(BinderInfo::Default, nat_type.clone(), {
        let a = Expr::bvar(0);
        Expr::app(Expr::app(nat_dvd.clone(), a), nat_zero.clone())
    });
    assert_eq!(dvd_zero_info.type_, expected_dvd_zero_type);
}

#[test]
fn test_nat_gcd_assoc_type() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_gcd = Expr::const_(Name::from_string("Nat.gcd"), vec![]);

    // Check Nat.gcd_assoc : ∀ a b c : Nat, Eq (gcd (gcd a b) c) (gcd a (gcd b c))
    let gcd_assoc_info = env.get_const(&Name::from_string("Nat.gcd_assoc")).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::pi(BinderInfo::Default, nat_type.clone(), {
                let a = Expr::bvar(2);
                let b = Expr::bvar(1);
                let c = Expr::bvar(0);
                let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), b.clone());
                let lhs = Expr::app(Expr::app(nat_gcd.clone(), gcd_a_b), c.clone());
                let gcd_b_c = Expr::app(Expr::app(nat_gcd.clone(), b), c);
                let rhs = Expr::app(Expr::app(nat_gcd.clone(), a), gcd_b_c);
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat_type.clone(),
                        ),
                        lhs,
                    ),
                    rhs,
                )
            }),
        ),
    );
    assert_eq!(gcd_assoc_info.type_, expected_type);
}

#[test]
fn test_nat_lcm_assoc_type() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_lcm = Expr::const_(Name::from_string("Nat.lcm"), vec![]);

    // Check Nat.lcm_assoc : ∀ a b c : Nat, Eq (lcm (lcm a b) c) (lcm a (lcm b c))
    let lcm_assoc_info = env.get_const(&Name::from_string("Nat.lcm_assoc")).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::pi(BinderInfo::Default, nat_type.clone(), {
                let a = Expr::bvar(2);
                let b = Expr::bvar(1);
                let c = Expr::bvar(0);
                let lcm_a_b = Expr::app(Expr::app(nat_lcm.clone(), a.clone()), b.clone());
                let lhs = Expr::app(Expr::app(nat_lcm.clone(), lcm_a_b), c.clone());
                let lcm_b_c = Expr::app(Expr::app(nat_lcm.clone(), b), c);
                let rhs = Expr::app(Expr::app(nat_lcm.clone(), a), lcm_b_c);
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat_type.clone(),
                        ),
                        lhs,
                    ),
                    rhs,
                )
            }),
        ),
    );
    assert_eq!(lcm_assoc_info.type_, expected_type);
}

#[test]
fn test_nat_gcd_zero_properties() {
    let mut env = Environment::new();
    env.init_nat_gcd().unwrap();

    // Verify all zero/one/self properties are registered
    for s in [
        "Nat.gcd_zero_left",
        "Nat.gcd_zero_right",
        "Nat.lcm_zero_left",
        "Nat.lcm_zero_right",
        "Nat.gcd_one_left",
        "Nat.gcd_one_right",
        "Nat.gcd_self",
        "Nat.lcm_self",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_gcd_monoid_init() {
    let mut env = Environment::new();
    env.init_gcd_monoid().unwrap();

    // Check GcdMonoid type and constructor are registered
    assert_ind(&env, "GcdMonoid");
    assert_const(&env, "GcdMonoid.mk");
}

#[test]
fn test_gcd_monoid_idempotent() {
    let mut env = Environment::new();
    env.init_gcd_monoid().unwrap();
    // Second call should be no-op
    env.init_gcd_monoid().unwrap();
    assert!(env.has_gcd_monoid());
}

#[test]
fn test_nat_gcd_monoid_inst_init() {
    let mut env = Environment::new();
    env.init_nat_gcd_monoid_inst().unwrap();

    // Check instance is registered
    assert_const(&env, "instGcdMonoidNat");
    assert!(env.has_nat_gcd_monoid_inst());
}

#[test]
fn test_nat_gcd_monoid_inst_idempotent() {
    let mut env = Environment::new();
    env.init_nat_gcd_monoid_inst().unwrap();
    // Second call should be no-op
    env.init_nat_gcd_monoid_inst().unwrap();
    assert!(env.has_nat_gcd_monoid_inst());
}

#[test]
fn test_nat_gcd_monoid_inst_type_check() {
    let mut env = Environment::new();
    env.init_nat_gcd_monoid_inst().unwrap();

    // Verify the instance has the correct type: GcdMonoid.{0} Nat
    // Nat : Type 0, so GcdMonoid universe parameter u = 0
    let inst = env
        .get_const(&Name::from_string("instGcdMonoidNat"))
        .unwrap();
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("GcdMonoid"), vec![Level::zero()]),
        nat_type,
    );
    assert_eq!(inst.type_, expected_type);
}

#[test]
fn test_nat_prime_init() {
    let mut env = Environment::new();
    env.init_nat_prime().unwrap();

    // Check Nat.Prime type and properties are registered
    for s in [
        "Nat.Prime",
        "Nat.Prime.ne_zero",
        "Nat.Prime.ne_one",
        "Nat.Prime.dvd_mul",
        "Nat.prime_two",
        "Nat.prime_three",
        "Nat.exists_prime_and_dvd",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_prime_idempotent() {
    let mut env = Environment::new();
    env.init_nat_prime().unwrap();
    // Second call should be no-op
    env.init_nat_prime().unwrap();
    assert!(env.has_nat_prime());
}

#[test]
fn test_nat_prime_type() {
    let mut env = Environment::new();
    env.init_nat_prime().unwrap();

    // Check Nat.Prime : Nat → Prop
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let prime_info = env.get_const(&Name::from_string("Nat.Prime")).unwrap();
    let expected_type = Expr::pi(BinderInfo::Default, nat_type, prop);
    assert_eq!(prime_info.type_, expected_type);
}

#[test]
fn test_nat_prime_two_type() {
    let mut env = Environment::new();
    env.init_nat_prime().unwrap();

    // Check Nat.prime_two : Prime 2
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        nat_zero.clone(),
    );
    let two = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), nat_one);
    let prime_two_info = env.get_const(&Name::from_string("Nat.prime_two")).unwrap();
    let expected_type = Expr::app(Expr::const_(Name::from_string("Nat.Prime"), vec![]), two);
    assert_eq!(prime_two_info.type_, expected_type);
}

// ==================== Irreducible Tests ====================

#[test]
fn test_irreducible_init() {
    let mut env = Environment::new();
    env.init_irreducible().unwrap();

    // Check Irreducible type and properties are registered
    for s in [
        "Irreducible",
        "Irreducible.ne_zero",
        "Nat.Irreducible",
        "Nat.Prime.irreducible",
        "Nat.Irreducible.prime",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_irreducible_idempotent() {
    let mut env = Environment::new();
    env.init_irreducible().unwrap();
    // Second call should be no-op
    env.init_irreducible().unwrap();
    assert!(env.has_irreducible());
}

#[test]
fn test_nat_irreducible_type() {
    let mut env = Environment::new();
    env.init_irreducible().unwrap();

    // Check Nat.Irreducible : Nat → Prop
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let irr_info = env
        .get_const(&Name::from_string("Nat.Irreducible"))
        .unwrap();
    let expected_type = Expr::pi(BinderInfo::Default, nat_type, prop);
    assert_eq!(irr_info.type_, expected_type);
}

// ==================== Associated Tests ====================

#[test]
fn test_associated_init() {
    let mut env = Environment::new();
    env.init_associated().unwrap();

    // Check Associated type and properties are registered
    for s in [
        "Associated",
        "Associated.refl",
        "Associated.symm",
        "Associated.trans",
        "Nat.Associated",
        "Nat.Associated.eq",
        "Nat.eq_associated",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_associated_idempotent() {
    let mut env = Environment::new();
    env.init_associated().unwrap();
    // Second call should be no-op
    env.init_associated().unwrap();
    assert!(env.has_associated());
}

#[test]
fn test_nat_associated_type() {
    let mut env = Environment::new();
    env.init_associated().unwrap();

    // Check Nat.Associated : Nat → Nat → Prop
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let assoc_info = env.get_const(&Name::from_string("Nat.Associated")).unwrap();
    let expected_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(BinderInfo::Default, nat_type, prop),
    );
    assert_eq!(assoc_info.type_, expected_type);
}

// ==================== UFM Tests ====================

#[test]
fn test_ufm_init() {
    let mut env = Environment::new();
    env.init_ufm().unwrap();

    // Check UniqueFactorizationMonoid type is registered
    assert_const(&env, "UniqueFactorizationMonoid");
}

#[test]
fn test_ufm_idempotent() {
    let mut env = Environment::new();
    env.init_ufm().unwrap();
    // Second call should be no-op
    env.init_ufm().unwrap();
    assert!(env.has_ufm());
}

#[test]
fn test_nat_ufm_inst_init() {
    let mut env = Environment::new();
    env.init_nat_ufm_inst().unwrap();

    // Check Nat UFM instance and prime factorization properties
    for s in [
        "Nat.instUniqueFactorizationMonoid",
        "Nat.prime_dvd_prime_mul",
        "Nat.eq_one_of_self_mul_self",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_ufm_inst_idempotent() {
    let mut env = Environment::new();
    env.init_nat_ufm_inst().unwrap();
    // Second call should be no-op
    env.init_nat_ufm_inst().unwrap();
    assert!(env.has_nat_ufm_inst());
}

#[test]
fn test_ufm_dependencies() {
    let mut env = Environment::new();
    env.init_ufm().unwrap();

    // UFM should have initialized its dependencies
    assert!(env.has_associated());
    assert!(env.has_irreducible());
    assert!(env.has_gcd_monoid());
}

#[test]
fn test_nat_ufm_prime_dvd_prime_mul_type() {
    let mut env = Environment::new();
    env.init_nat_ufm_inst().unwrap();

    // Check Nat.prime_dvd_prime_mul has correct arity
    let prime_dvd_info = env
        .get_const(&Name::from_string("Nat.prime_dvd_prime_mul"))
        .unwrap();
    // Type should start with implicit Nat arguments
    if let ExprKind::Pi(binder_info, _, _) = &prime_dvd_info.type_.kind {
        assert_eq!(binder_info.info, BinderInfo::Implicit);
    } else {
        panic!("Expected Pi type");
    }
}

// ==================== Rat Type Tests ====================

#[test]
fn test_rat_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat());
    env.init_rat().unwrap();
    assert!(env.has_rat());

    // WS-A: `Rat` is the QUOTIENT carrier; `Rat.mk` is the quotient
    // constructor; the well-defined-on-representatives projections live under
    // `Rat.Raw.*` (the quotient identifies equivalent fractions, so num/denom
    // are not well-defined on `Rat` itself).
    for s in [
        "Rat",
        "Rat.mk",
        "Rat.Raw.num",
        "Rat.Raw.denom",
        "Rat.zero",
        "Rat.one",
    ] {
        assert_const(&env, s);
    }
    assert!(
        env.get_inductive(&Name::from_string("Rat.Raw")).is_some(),
        "Rat.Raw pre-quotient carrier must be registered"
    );
}

#[test]
fn test_rat_idempotent() {
    let mut env = Environment::new();
    env.init_rat().unwrap();
    env.init_rat().unwrap(); // Should be idempotent
    assert!(env.has_rat());
}

#[test]
fn test_rat_type() {
    let mut env = Environment::new();
    env.init_rat().unwrap();

    // Rat : Type
    let rat_info = env.get_const(&Name::from_string("Rat")).unwrap();
    assert!(matches!(&rat_info.type_.kind, ExprKind::Sort(_)));
}

#[test]
fn test_rat_mk_type() {
    let mut env = Environment::new();
    env.init_rat().unwrap();

    // Rat.mk : Int → Nat → Rat
    let mk_info = env.get_const(&Name::from_string("Rat.mk")).unwrap();
    // Should be Pi(Int, Pi(Nat, Rat))
    if let ExprKind::Pi(_, domain, _) = &mk_info.type_.kind {
        // domain should be Int
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Int");
        } else {
            panic!("Expected Const Int");
        }
    } else {
        panic!("Expected Pi type");
    }
}

#[test]
fn test_rat_num_type() {
    let mut env = Environment::new();
    env.init_rat().unwrap();

    // WS-A: num projects a representative, so it lives on the pre-quotient
    // carrier: Rat.Raw.num : Rat.Raw → Int.
    let num_info = env.get_const(&Name::from_string("Rat.Raw.num")).unwrap();
    if let ExprKind::Pi(_, domain, codomain) = &num_info.type_.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat.Raw");
        }
        if let ExprKind::Const(name, _) = &codomain.as_ref().kind {
            assert_eq!(name.to_string(), "Int");
        }
    } else {
        panic!("Expected Pi type");
    }
}

#[test]
fn test_rat_denom_type() {
    let mut env = Environment::new();
    env.init_rat().unwrap();

    // WS-A: Rat.Raw.denom : Rat.Raw → Nat (representative projection).
    let denom_info = env.get_const(&Name::from_string("Rat.Raw.denom")).unwrap();
    if let ExprKind::Pi(_, domain, codomain) = &denom_info.type_.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat.Raw");
        }
        if let ExprKind::Const(name, _) = &codomain.as_ref().kind {
            assert_eq!(name.to_string(), "Nat");
        }
    } else {
        panic!("Expected Pi type");
    }
}

#[test]
fn test_rat_arith_init() {
    let mut env = Environment::new();
    env.init_rat_arith().unwrap();

    // Check arithmetic operations exist
    for s in [
        "Rat.neg", "Rat.add", "Rat.sub", "Rat.mul", "Rat.inv", "Rat.div",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_arith_idempotent() {
    let mut env = Environment::new();
    env.init_rat_arith().unwrap();
    env.init_rat_arith().unwrap(); // Must be idempotent - was broken before rat_arith_init flag
    assert!(env.has_rat_arith());
}

#[test]
fn test_rat_neg_type() {
    let mut env = Environment::new();
    env.init_rat_arith().unwrap();

    // Rat.neg : Rat → Rat
    let neg_info = env.get_const(&Name::from_string("Rat.neg")).unwrap();
    if let ExprKind::Pi(_, domain, codomain) = &neg_info.type_.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
        if let ExprKind::Const(name, _) = &codomain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
    } else {
        panic!("Expected Pi type");
    }
}

#[test]
fn test_rat_add_type() {
    let mut env = Environment::new();
    env.init_rat_arith().unwrap();

    // Rat.add : Rat → Rat → Rat
    let add_info = env.get_const(&Name::from_string("Rat.add")).unwrap();
    if let ExprKind::Pi(_, domain, rest) = &add_info.type_.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
        if let ExprKind::Pi(_, _, codomain) = &rest.as_ref().kind {
            if let ExprKind::Const(name, _) = &codomain.as_ref().kind {
                assert_eq!(name.to_string(), "Rat");
            }
        }
    } else {
        panic!("Expected Pi type");
    }
}

#[test]
fn test_rat_normalize_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_normalize());
    env.init_rat_normalize().unwrap();
    assert!(env.has_rat_normalize());
    assert_const(&env, "Rat.normalize");
}

#[test]
fn test_rat_normalize_idempotent() {
    let mut env = Environment::new();
    env.init_rat_normalize().unwrap();
    env.init_rat_normalize().unwrap();
    assert!(env.has_rat_normalize());
}

#[test]
fn test_rat_normalize_type() {
    let mut env = Environment::new();
    env.init_rat_normalize().unwrap();

    let norm_info = env.get_const(&Name::from_string("Rat.normalize")).unwrap();
    if let ExprKind::Pi(_, domain, codomain) = &norm_info.type_.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
        if let ExprKind::Const(name, _) = &codomain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
    } else {
        panic!("Expected Pi type");
    }
}

// ===========================================
// Tests for Rat ordering
// ===========================================

#[test]
fn test_rat_ord_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_ord());
    env.init_rat_ord().unwrap();
    assert!(env.has_rat_ord());

    // Check all ordering definitions exist
    for s in ["Rat.le", "Rat.lt", "instLERat", "instLTRat"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_ord_idempotent() {
    let mut env = Environment::new();
    env.init_rat_ord().unwrap();
    env.init_rat_ord().unwrap();
    env.init_rat_ord().unwrap();
    assert!(env.has_rat_ord());
}

#[test]
fn test_rat_le_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ord().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let prop_const = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Rat.le : Rat → Rat → Prop
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let rat_le_ty = tc.infer_type(&rat_le).unwrap();

    let expected_ty = Expr::pi(
        BinderInfo::Default,
        rat_const.clone(),
        Expr::pi(BinderInfo::Default, rat_const.clone(), prop_const),
    );

    assert!(tc.is_def_eq(&rat_le_ty, &expected_ty));
}

#[test]
fn test_rat_lt_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ord().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let prop_const = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Rat.lt : Rat → Rat → Prop
    let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
    let rat_lt_ty = tc.infer_type(&rat_lt).unwrap();

    let expected_ty = Expr::pi(
        BinderInfo::Default,
        rat_const.clone(),
        Expr::pi(BinderInfo::Default, rat_const.clone(), prop_const),
    );

    assert!(tc.is_def_eq(&rat_lt_ty, &expected_ty));
}

#[test]
fn test_inst_le_rat_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ord().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

    // instLERat : LE Rat
    // LE : Type u → Type u, Rat : Type 0, so LE.{0}
    let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);
    let inst_le_rat_ty = tc.infer_type(&inst_le_rat).unwrap();

    let expected_ty = Expr::app(
        Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
        rat_const,
    );

    assert!(tc.is_def_eq(&inst_le_rat_ty, &expected_ty));
}

#[test]
fn test_inst_lt_rat_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ord().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

    // instLTRat : LT Rat
    // LT : Type u → Type u, Rat : Type 0, so LT.{0}
    let inst_lt_rat = Expr::const_(Name::from_string("instLTRat"), vec![]);
    let inst_lt_rat_ty = tc.infer_type(&inst_lt_rat).unwrap();

    let expected_ty = Expr::app(
        Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
        rat_const,
    );

    assert!(tc.is_def_eq(&inst_lt_rat_ty, &expected_ty));
}

// ===========================================
// Tests for Rat LinearOrder instance
// ===========================================

#[test]
fn test_rat_linear_order_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_linear_order());
    env.init_rat_linear_order().unwrap();
    assert!(env.has_rat_linear_order());

    // Check all ordering axioms and instances exist
    for s in [
        "Rat.le_refl",
        "Rat.le_trans",
        "Rat.le_antisymm",
        "Rat.lt_iff_le_not_le",
        "Rat.le_total",
        "instPreorderRat",
        "instPartialOrderRat",
        "instLinearOrderRat",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_linear_order_idempotent() {
    let mut env = Environment::new();
    env.init_rat_linear_order().unwrap();
    env.init_rat_linear_order().unwrap();
    env.init_rat_linear_order().unwrap();
    assert!(env.has_rat_linear_order());
}

#[test]
fn test_rat_linear_order_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_linear_order().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

    // instPreorderRat : Preorder Rat
    // Preorder : Type u → Type u, Rat : Type 0, so Preorder.{0}
    let preorder_rat = Expr::const_(Name::from_string("instPreorderRat"), vec![]);
    let preorder_rat_ty = tc.infer_type(&preorder_rat).unwrap();
    let expected_preorder_ty = Expr::app(
        Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
        rat_const.clone(),
    );
    assert!(tc.is_def_eq(&preorder_rat_ty, &expected_preorder_ty));

    // instPartialOrderRat : PartialOrder Rat
    // PartialOrder : Type u → Type u, Rat : Type 0, so PartialOrder.{0}
    let partial_order_rat = Expr::const_(Name::from_string("instPartialOrderRat"), vec![]);
    let partial_order_rat_ty = tc.infer_type(&partial_order_rat).unwrap();
    let expected_partial_order_ty = Expr::app(
        Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
        rat_const.clone(),
    );
    assert!(tc.is_def_eq(&partial_order_rat_ty, &expected_partial_order_ty));

    // instLinearOrderRat : LinearOrder Rat
    // LinearOrder : Type u → Type u, Rat : Type 0, so LinearOrder.{0}
    let linear_order_rat = Expr::const_(Name::from_string("instLinearOrderRat"), vec![]);
    let linear_order_rat_ty = tc.infer_type(&linear_order_rat).unwrap();
    let expected_linear_order_ty = Expr::app(
        Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
        rat_const.clone(),
    );
    assert!(tc.is_def_eq(&linear_order_rat_ty, &expected_linear_order_ty));
}

#[test]
fn test_rat_le_total_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_linear_order().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let or_const = Expr::const_(Name::from_string("Or"), vec![]);

    // Rat.le_total : ∀ a b : Rat, Or (Rat.le a b) (Rat.le b a)
    let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
    let le_total_ty = tc.infer_type(&le_total).unwrap();

    // Build expected type
    let expected_ty = Expr::pi(
        BinderInfo::Default,
        rat_const.clone(),
        Expr::pi(
            BinderInfo::Default,
            rat_const.clone(),
            Expr::app(
                Expr::app(
                    or_const.clone(),
                    Expr::app(Expr::app(le_const.clone(), Expr::bvar(1)), Expr::bvar(0)),
                ),
                Expr::app(Expr::app(le_const.clone(), Expr::bvar(0)), Expr::bvar(1)),
            ),
        ),
    );

    assert!(tc.is_def_eq(&le_total_ty, &expected_ty));
}

// ===========================================
// Tests for Rat Field instance
// ===========================================

#[test]
fn test_rat_field_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_field_inst());
    env.init_rat_field_inst().unwrap();
    assert!(env.has_rat_field_inst());

    // Check Field instance exists
    let inst_info = env.get_const(&Name::from_string("instFieldRat")).unwrap();

    // Type should be Field Rat
    if let ExprKind::App(field, rat) = &inst_info.type_.kind {
        if let ExprKind::Const(name, _) = &field.as_ref().kind {
            assert_eq!(name.to_string(), "Field");
        }
        if let ExprKind::Const(name, _) = &rat.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
    } else {
        panic!("Expected App type");
    }
}

#[test]
fn test_rat_field_inst_idempotent() {
    let mut env = Environment::new();
    env.init_rat_field_inst().unwrap();
    env.init_rat_field_inst().unwrap(); // Should be idempotent
    assert!(env.has_rat_field_inst());
}

#[test]
fn test_rat_field_axioms() {
    let mut env = Environment::new();
    env.init_rat_field_inst().unwrap();

    // Check all field axioms exist
    for s in [
        "Rat.add_assoc",
        "Rat.zero_add",
        "Rat.add_zero",
        "Rat.add_comm",
        "Rat.mul_assoc",
        "Rat.one_mul",
        "Rat.mul_one",
        "Rat.zero_mul",
        "Rat.mul_zero",
        "Rat.left_distrib",
        "Rat.right_distrib",
        "Rat.add_left_neg",
        "Rat.mul_comm",
        "Rat.mul_inv_cancel",
        "Rat.inv_zero",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_dependencies() {
    let mut env = Environment::new();
    env.init_rat_field_inst().unwrap();

    // Rat Field instance should initialize all dependencies
    assert!(env.has_rat());
    assert!(env.has_int());
    assert!(env.has_nat());
    assert!(env.has_field());
}

// ===========================================
// Tests for LinearOrderedField typeclass
// ===========================================

#[test]
fn test_linear_ordered_field_init() {
    let mut env = Environment::new();
    assert!(!env.has_linear_ordered_field());
    env.init_linear_ordered_field().unwrap();
    assert!(env.has_linear_ordered_field());

    // Check LinearOrderedField type exists
    assert!(env
        .get_const(&Name::from_string("LinearOrderedField"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("LinearOrderedField.mk"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("LinearOrderedField.rec"))
        .is_some());
}

#[test]
fn test_linear_ordered_field_idempotent() {
    let mut env = Environment::new();
    env.init_linear_ordered_field().unwrap();
    env.init_linear_ordered_field().unwrap(); // Should be idempotent
    assert!(env.has_linear_ordered_field());
}

#[test]
fn test_linear_ordered_field_projections() {
    let mut env = Environment::new();
    env.init_linear_ordered_field().unwrap();

    // Check projections exist
    assert!(env
        .get_const(&Name::from_string("LinearOrderedField.toField"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("LinearOrderedField.toLinearOrder"))
        .is_some());
}

#[test]
fn test_linear_ordered_field_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_linear_ordered_field().unwrap();

    let tc = TypeChecker::new(&env);

    // LinearOrderedField inductive should type check
    let lof = env
        .get_const(&Name::from_string("LinearOrderedField"))
        .unwrap();
    let _ = tc.infer_type(&lof.type_).unwrap();

    // Projection types should type check (checking the type of the type)
    let to_field = env
        .get_const(&Name::from_string("LinearOrderedField.toField"))
        .unwrap();
    let _ = tc.infer_type(&to_field.type_).unwrap();

    // Note: toLinearOrder projection value uses complex recursor application
    // The projection type itself is well-formed, even if the value definition
    // has universe issues in the minor premise bindings (which use Prop placeholders)
    let to_lo = env
        .get_const(&Name::from_string("LinearOrderedField.toLinearOrder"))
        .unwrap();
    // Check projection type is well-formed (not the value)
    let to_lo_ty = tc
        .infer_type(&to_lo.type_)
        .expect("toLinearOrder projection type should be well-formed");
    assert!(
        matches!(&to_lo_ty.kind, ExprKind::Sort(..) | ExprKind::Pi(..)),
        "projection type should be Sort or Pi, got {:?}",
        to_lo_ty.kind
    );
}

fn expr_contains_proj(expr: &Expr, struct_name: &Name, idx: u32) -> bool {
    match &expr.kind {
        ExprKind::Proj(name, proj_idx, inner) => {
            (*proj_idx == idx && name == struct_name) || expr_contains_proj(inner, struct_name, idx)
        }
        ExprKind::App(f, a) => {
            expr_contains_proj(f, struct_name, idx) || expr_contains_proj(a, struct_name, idx)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_proj(ty, struct_name, idx) || expr_contains_proj(body, struct_name, idx)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_proj(ty, struct_name, idx)
                || expr_contains_proj(val, struct_name, idx)
                || expr_contains_proj(body, struct_name, idx)
        }
        ExprKind::MData(_, inner) => expr_contains_proj(inner, struct_name, idx),
        _ => false,
    }
}

fn expr_contains_rec_const(expr: &Expr) -> bool {
    expr.collect_constants()
        .iter()
        .any(|name| name.to_string().ends_with(".rec"))
}

#[test]
fn test_issue1413_projection_values_use_proj_numeric_families() {
    let mut env = Environment::new();
    env.init_group().unwrap();
    env.init_add_group().unwrap();
    env.init_comm_ring().unwrap();
    env.init_field().unwrap();
    env.init_integral_domain().unwrap();
    env.init_well_founded().unwrap();
    env.init_linear_ordered_field().unwrap();

    let checks = [
        ("Group.mul", "Group", 0),
        ("AddGroup.add", "AddGroup", 0),
        ("CommRing.mul", "CommRing", 6),
        ("Field.inv", "Field", 17),
        ("IntegralDomain.neg", "IntegralDomain", 15),
        ("WellFounded.apply", "WellFounded", 0),
        ("LinearOrderedField.toField", "LinearOrderedField", 0),
        ("LinearOrderedField.toLinearOrder", "LinearOrderedField", 1),
    ];

    for (decl_name, struct_name, field_idx) in checks {
        let info = env
            .get_const(&Name::from_string(decl_name))
            .unwrap_or_else(|| panic!("{decl_name} should exist"));
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{decl_name} should have a value"));
        let struct_name = Name::from_string(struct_name);

        assert!(
            expr_contains_proj(value, &struct_name, field_idx),
            "{decl_name} should include Expr::proj({struct_name}, {field_idx}, ...)"
        );
        assert!(
            !expr_contains_rec_const(value),
            "{decl_name} should not depend on .rec constants after #1413 migration"
        );
    }
}

// ===========================================
// Tests for Rat ordered field axioms
// ===========================================

#[test]
fn test_rat_ordered_field_axioms_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_ordered_field_axioms());
    env.init_rat_ordered_field_axioms().unwrap();
    assert!(env.has_rat_ordered_field_axioms());

    // Check axioms exist
    for s in ["Rat.add_le_add_left", "Rat.mul_pos", "Rat.zero_lt_one"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_ordered_field_axioms_idempotent() {
    let mut env = Environment::new();
    env.init_rat_ordered_field_axioms().unwrap();
    env.init_rat_ordered_field_axioms().unwrap(); // Should be idempotent
    assert!(env.has_rat_ordered_field_axioms());
}

#[test]
fn test_rat_ordered_field_axioms_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ordered_field_axioms().unwrap();

    let tc = TypeChecker::new(&env);

    // Rat.add_le_add_left type check
    let add_le_add_left = env
        .get_const(&Name::from_string("Rat.add_le_add_left"))
        .unwrap();
    let _ = tc.infer_type(&add_le_add_left.type_).unwrap();

    // Rat.mul_pos type check
    let mul_pos = env.get_const(&Name::from_string("Rat.mul_pos")).unwrap();
    let _ = tc.infer_type(&mul_pos.type_).unwrap();

    // Rat.zero_lt_one : Rat.lt Rat.zero Rat.one
    let zero_lt_one = env
        .get_const(&Name::from_string("Rat.zero_lt_one"))
        .unwrap();
    let zero_lt_one_ty = tc.infer_type(&zero_lt_one.type_).unwrap();
    // Type of a Prop is Prop
    assert!(tc.is_def_eq(
        &zero_lt_one_ty,
        &Expr::from_kind(ExprKind::Sort(Level::zero()))
    ));
}

// ===========================================
// Tests for Rat LinearOrderedField instance
// ===========================================

#[test]
fn test_rat_linear_ordered_field_inst_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_linear_ordered_field_inst());
    env.init_rat_linear_ordered_field_inst().unwrap();
    assert!(env.has_rat_linear_ordered_field_inst());

    // Check instance exists
    let inst_info = env
        .get_const(&Name::from_string("instLinearOrderedFieldRat"))
        .unwrap();

    // Type should be LinearOrderedField Rat
    if let ExprKind::App(lof, rat) = &inst_info.type_.kind {
        if let ExprKind::Const(name, _) = &lof.as_ref().kind {
            assert_eq!(name.to_string(), "LinearOrderedField");
        }
        if let ExprKind::Const(name, _) = &rat.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        }
    } else {
        panic!("Expected App type for LinearOrderedField Rat");
    }
}

#[test]
fn test_rat_linear_ordered_field_inst_idempotent() {
    let mut env = Environment::new();
    env.init_rat_linear_ordered_field_inst().unwrap();
    env.init_rat_linear_ordered_field_inst().unwrap(); // Should be idempotent
    assert!(env.has_rat_linear_ordered_field_inst());
}

#[test]
fn test_rat_linear_ordered_field_inst_type_checks() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_linear_ordered_field_inst().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

    // instLinearOrderedFieldRat : LinearOrderedField Rat
    // LinearOrderedField : Type u → Type u, Rat : Type 0, so LinearOrderedField.{0}
    let inst = Expr::const_(Name::from_string("instLinearOrderedFieldRat"), vec![]);
    let inst_ty = tc.infer_type(&inst).unwrap();
    let expected_ty = Expr::app(
        Expr::const_(Name::from_string("LinearOrderedField"), vec![Level::zero()]),
        rat_const.clone(),
    );
    assert!(tc.is_def_eq(&inst_ty, &expected_ty));
}

#[test]
fn test_rat_linear_ordered_field_dependencies() {
    let mut env = Environment::new();
    env.init_rat_linear_ordered_field_inst().unwrap();

    // Should initialize all dependencies
    assert!(env.has_linear_ordered_field());
    assert!(env.has_rat_field_inst());
    assert!(env.has_rat_linear_order());
    assert!(env.has_rat_ordered_field_axioms());
}

// ===========================================
// Rat Decidable Ordering Tests
// ===========================================

#[test]
fn test_rat_decidable_ord_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_decidable_ord());
    env.init_rat_decidable_ord().unwrap();
    assert!(env.has_rat_decidable_ord());

    // Check both instances and decEq exist
    for s in ["instDecidableRatLt", "instDecidableRatLe", "Rat.decEq"] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_decidable_ord_idempotent() {
    let mut env = Environment::new();
    env.init_rat_decidable_ord().unwrap();
    env.init_rat_decidable_ord().unwrap(); // Should be idempotent
    assert!(env.has_rat_decidable_ord());
}

#[test]
fn test_rat_decidable_lt_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_decidable_ord().unwrap();

    // instDecidableRatLt : ∀ a b : Rat, Decidable (Rat.lt a b)
    let decidable_lt = env
        .get_const(&Name::from_string("instDecidableRatLt"))
        .unwrap();
    assert_eq!(decidable_lt.value, None); // axiom has no value

    // Type check the instance
    let tc = TypeChecker::new(&env);
    let inst = Expr::const_(Name::from_string("instDecidableRatLt"), vec![]);
    let inst_ty = tc.infer_type(&inst).unwrap();

    // Should be Pi type: ∀ a b : Rat, Decidable (Rat.lt a b)
    if let ExprKind::Pi(_, domain, _) = &inst_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {inst_ty:?}");
    }
}

#[test]
fn test_rat_decidable_le_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_decidable_ord().unwrap();

    // instDecidableRatLe : ∀ a b : Rat, Decidable (Rat.le a b)
    let decidable_le = env
        .get_const(&Name::from_string("instDecidableRatLe"))
        .unwrap();
    assert_eq!(decidable_le.value, None); // axiom has no value

    // Type check the instance
    let tc = TypeChecker::new(&env);
    let inst = Expr::const_(Name::from_string("instDecidableRatLe"), vec![]);
    let inst_ty = tc.infer_type(&inst).unwrap();

    // Should be Pi type: ∀ a b : Rat, Decidable (Rat.le a b)
    if let ExprKind::Pi(_, domain, _) = &inst_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {inst_ty:?}");
    }
}

#[test]
fn test_rat_dec_eq_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_decidable_ord().unwrap();

    // Rat.decEq : ∀ a b : Rat, Decidable (Eq a b)
    let dec_eq = env.get_const(&Name::from_string("Rat.decEq")).unwrap();
    assert_eq!(dec_eq.value, None); // axiom has no value

    // Type check the instance
    let tc = TypeChecker::new(&env);
    let inst = Expr::const_(Name::from_string("Rat.decEq"), vec![]);
    let inst_ty = tc.infer_type(&inst).unwrap();

    // Should be Pi type: ∀ a b : Rat, Decidable (Eq Rat a b)
    if let ExprKind::Pi(_, domain, _) = &inst_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {inst_ty:?}");
    }
}

#[test]
fn test_rat_decidable_ord_dependencies() {
    let mut env = Environment::new();
    env.init_rat_decidable_ord().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_rat_ord());
    assert!(env.has_decidable());
    assert!(env.has_eq());
}

// ===========================================
// Rat Min/Max Tests
// ===========================================

#[test]
fn test_rat_minmax_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_minmax());
    env.init_rat_minmax().unwrap();
    assert!(env.has_rat_minmax());

    // Check functions and characterizing axioms exist
    for s in [
        "Rat.min",
        "Rat.max",
        "Rat.min_def",
        "Rat.min_def'",
        "Rat.max_def",
        "Rat.max_def'",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_minmax_idempotent() {
    let mut env = Environment::new();
    env.init_rat_minmax().unwrap();
    env.init_rat_minmax().unwrap(); // Should be idempotent
    assert!(env.has_rat_minmax());
}

#[test]
fn test_rat_min_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_minmax().unwrap();

    // Rat.min : Rat → Rat → Rat
    // WS-B: now a reducible Definition (was a bodyless Axiom), so it has a value.
    let min_info = env.get_const(&Name::from_string("Rat.min")).unwrap();
    assert!(min_info.value.is_some());

    let tc = TypeChecker::new(&env);
    let min_const = Expr::const_(Name::from_string("Rat.min"), vec![]);
    let min_ty = tc.infer_type(&min_const).unwrap();

    // Should be Rat → Rat → Rat
    if let ExprKind::Pi(_, domain, _) = &min_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {min_ty:?}");
    }
}

#[test]
fn test_rat_max_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_minmax().unwrap();

    // Rat.max : Rat → Rat → Rat
    // WS-B: now a reducible Definition (was a bodyless Axiom), so it has a value.
    let max_info = env.get_const(&Name::from_string("Rat.max")).unwrap();
    assert!(max_info.value.is_some());

    let tc = TypeChecker::new(&env);
    let max_const = Expr::const_(Name::from_string("Rat.max"), vec![]);
    let max_ty = tc.infer_type(&max_const).unwrap();

    // Should be Rat → Rat → Rat
    if let ExprKind::Pi(_, domain, _) = &max_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {max_ty:?}");
    }
}

#[test]
fn test_rat_min_def_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_minmax().unwrap();

    // Rat.min_def : ∀ a b : Rat, Rat.le a b → Eq (Rat.min a b) a
    // WS-B: now a constructive Theorem (was a bodyless Axiom), so it has a value.
    let min_def_info = env.get_const(&Name::from_string("Rat.min_def")).unwrap();
    assert!(min_def_info.value.is_some());

    let tc = TypeChecker::new(&env);
    let min_def = Expr::const_(Name::from_string("Rat.min_def"), vec![]);
    let min_def_ty = tc.infer_type(&min_def).unwrap();

    // Should be Pi type: ∀ a : Rat, ...
    if let ExprKind::Pi(_, domain, _) = &min_def_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {min_def_ty:?}");
    }
}

#[test]
fn test_rat_max_def_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_minmax().unwrap();

    // Rat.max_def : ∀ a b : Rat, Rat.le a b → Eq (Rat.max a b) b
    // WS-B: now a constructive Theorem (was a bodyless Axiom), so it has a value.
    let max_def_info = env.get_const(&Name::from_string("Rat.max_def")).unwrap();
    assert!(max_def_info.value.is_some());

    let tc = TypeChecker::new(&env);
    let max_def = Expr::const_(Name::from_string("Rat.max_def"), vec![]);
    let max_def_ty = tc.infer_type(&max_def).unwrap();

    // Should be Pi type: ∀ a : Rat, ...
    if let ExprKind::Pi(_, domain, _) = &max_def_ty.kind {
        if let ExprKind::Const(name, _) = &domain.as_ref().kind {
            assert_eq!(name.to_string(), "Rat");
        } else {
            panic!("Expected Rat domain, got {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got {max_def_ty:?}");
    }
}

#[test]
fn test_rat_minmax_dependencies() {
    let mut env = Environment::new();
    env.init_rat_minmax().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_rat_ord());
    assert!(env.has_eq());
}

// ========================================
// Rat.abs tests
// ========================================

#[test]
fn test_rat_abs_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_abs());

    env.init_rat_abs().unwrap();
    assert!(env.has_rat_abs());

    // Check functions and axioms exist
    for s in [
        "Rat.abs",
        "Rat.abs_nonneg",
        "Rat.abs_of_nonneg",
        "Rat.abs_of_neg",
        "Rat.abs_zero",
        "Rat.abs_mul",
        "Rat.abs_add_le",
        "Rat.abs_sub_le",
        "Rat.abs_neg",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_abs_idempotent() {
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();
    env.init_rat_abs().unwrap(); // Should be idempotent
    assert!(env.has_rat_abs());
}

#[test]
fn test_rat_abs_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs : Rat → Rat
    let abs = Expr::const_(Name::from_string("Rat.abs"), vec![]);
    let tc = TypeChecker::new(&env);
    let abs_ty = tc.infer_type(&abs).unwrap();

    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let expected_ty = Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const);

    assert!(
        tc.is_def_eq(&abs_ty, &expected_ty),
        "Rat.abs should have type Rat → Rat"
    );
}

#[test]
fn test_rat_abs_nonneg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_nonneg : ∀ a : Rat, Rat.le Rat.zero (Rat.abs a)
    let abs_nonneg_info = env.get_const(&Name::from_string("Rat.abs_nonneg")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a Pi type
    if let ExprKind::Pi(_, ref domain, _) = &abs_nonneg_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(tc.is_def_eq(domain, &rat_const), "Domain should be Rat");
    } else {
        panic!("Expected Pi type, got {:?}", abs_nonneg_info.type_);
    }
}

#[test]
fn test_rat_abs_of_nonneg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_of_nonneg : ∀ a : Rat, Rat.le Rat.zero a → Eq (Rat.abs a) a
    let abs_of_nonneg_info = env
        .get_const(&Name::from_string("Rat.abs_of_nonneg"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type
    if let ExprKind::Pi(_, ref domain, ref codomain) = &abs_of_nonneg_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "Outer domain should be Rat"
        );
        // Inner type should be Pi (Rat.le ...) (Eq ...)
        if let ExprKind::Pi(_, _, _) = &codomain.as_ref().kind {
            // OK - nested Pi
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_of_nonneg_info.type_);
    }
}

#[test]
fn test_rat_abs_of_neg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_of_neg : ∀ a : Rat, Rat.lt a Rat.zero → Eq (Rat.abs a) (Rat.neg a)
    let abs_of_neg_info = env.get_const(&Name::from_string("Rat.abs_of_neg")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type
    if let ExprKind::Pi(_, ref domain, ref codomain) = &abs_of_neg_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "Outer domain should be Rat"
        );
        // Inner type should be Pi (Rat.lt ...) (Eq ...)
        if let ExprKind::Pi(_, _, _) = &codomain.as_ref().kind {
            // OK - nested Pi
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_of_neg_info.type_);
    }
}

#[test]
fn test_rat_abs_zero_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_zero : Eq (Rat.abs Rat.zero) Rat.zero
    let abs_zero_info = env.get_const(&Name::from_string("Rat.abs_zero")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's an Eq type (App of App of App)
    if let ExprKind::App(ref f1, _) = &abs_zero_info.type_.kind {
        if let ExprKind::App(ref f2, _) = &f1.as_ref().kind {
            if let ExprKind::App(ref eq_head, _) = &f2.as_ref().kind {
                if let ExprKind::Const(ref name, _) = &eq_head.as_ref().kind {
                    assert_eq!(name.to_string(), "Eq", "Should be Eq type");
                } else {
                    panic!("Expected Eq constant");
                }
            } else {
                panic!("Expected App");
            }
        } else {
            panic!("Expected App");
        }
    } else {
        panic!("Expected App type, got {:?}", abs_zero_info.type_);
    }

    // Verify the whole type type-checks — result should be a Sort (it's a Prop-valued type)
    let abs_zero_sort = tc.infer_type(&abs_zero_info.type_).unwrap();
    assert!(
        matches!(&abs_zero_sort.kind, ExprKind::Sort(..)),
        "type of Rat.abs_zero's type should be a Sort, got {:?}",
        abs_zero_sort.kind
    );
}

#[test]
fn test_rat_abs_mul_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_mul : ∀ a b : Rat, Eq (Rat.abs (Rat.mul a b)) (Rat.mul (Rat.abs a) (Rat.abs b))
    let abs_mul_info = env.get_const(&Name::from_string("Rat.abs_mul")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type
    if let ExprKind::Pi(_, ref domain, ref codomain) = &abs_mul_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "Outer domain should be Rat"
        );
        // Inner type should be Pi Rat (Eq ...)
        if let ExprKind::Pi(_, ref inner_domain, _) = &codomain.as_ref().kind {
            assert!(
                tc.is_def_eq(inner_domain, &rat_const),
                "Inner domain should be Rat"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_mul_info.type_);
    }
}

#[test]
fn test_rat_abs_dependencies() {
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_rat_ord());
    assert!(env.has_rat()); // Rat arithmetic is part of init_rat
    assert!(env.has_eq());
}

#[test]
fn test_rat_abs_add_le_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_add_le : ∀ a b : Rat, Rat.le (Rat.abs (Rat.add a b)) (Rat.add (Rat.abs a) (Rat.abs b))
    let abs_add_le_info = env.get_const(&Name::from_string("Rat.abs_add_le")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a b : Rat, Prop
    if let ExprKind::Pi(_, ref domain, ref codomain) = &abs_add_le_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "Outer domain should be Rat"
        );
        // Inner should be ∀ b : Rat, ...
        if let ExprKind::Pi(_, ref inner_domain, ref _inner_codomain) = &codomain.as_ref().kind {
            assert!(
                tc.is_def_eq(inner_domain, &rat_const),
                "Inner domain should be Rat"
            );
            // Codomain should be Prop (Rat.le ...)
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_add_le_info.type_);
    }
}

#[test]
fn test_rat_abs_sub_le_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_sub_le : ∀ a b : Rat, Rat.le (Rat.abs (Rat.sub a b)) (Rat.add (Rat.abs a) (Rat.abs b))
    let abs_sub_le_info = env.get_const(&Name::from_string("Rat.abs_sub_le")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a b : Rat, Prop
    if let ExprKind::Pi(_, ref domain, ref codomain) = &abs_sub_le_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "Outer domain should be Rat"
        );
        // Inner should be ∀ b : Rat, ...
        if let ExprKind::Pi(_, ref inner_domain, ref _inner_codomain) = &codomain.as_ref().kind {
            assert!(
                tc.is_def_eq(inner_domain, &rat_const),
                "Inner domain should be Rat"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_sub_le_info.type_);
    }
}

#[test]
fn test_rat_abs_neg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();

    // Rat.abs_neg : ∀ a : Rat, Eq (Rat.abs (Rat.neg a)) (Rat.abs a)
    let abs_neg_info = env.get_const(&Name::from_string("Rat.abs_neg")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a : Rat, Eq Rat ... ...
    if let ExprKind::Pi(_, ref domain, ref _codomain) = &abs_neg_info.type_.kind {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(tc.is_def_eq(domain, &rat_const), "Domain should be Rat");
        // Codomain should be Eq type (Prop)
    } else {
        panic!("Expected Pi type, got {:?}", abs_neg_info.type_);
    }
}

// ========================================
// Int.min/max tests
// ========================================

#[test]
fn test_int_minmax_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_minmax());

    env.init_int_minmax().unwrap();
    assert!(env.has_int_minmax());

    // Check functions and characterizing axioms exist
    for s in [
        "Int.min",
        "Int.max",
        "Int.min_def",
        "Int.min_def'",
        "Int.max_def",
        "Int.max_def'",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_minmax_idempotent() {
    let mut env = Environment::new();
    env.init_int_minmax().unwrap();
    env.init_int_minmax().unwrap(); // Should be idempotent
    assert!(env.has_int_minmax());
}

#[test]
fn test_int_min_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_minmax().unwrap();

    // Int.min : Int → Int → Int
    let min_info = env.get_const(&Name::from_string("Int.min")).unwrap();
    let tc = TypeChecker::new(&env);

    if let ExprKind::Pi(_, ref domain, ref codomain) = &min_info.type_.kind {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "Outer domain should be Int"
        );
        // Inner type should be Int → Int
        if let ExprKind::Pi(_, ref inner_domain, ref inner_codomain) = &codomain.as_ref().kind {
            assert!(
                tc.is_def_eq(inner_domain, &int_const),
                "Inner domain should be Int"
            );
            assert!(
                tc.is_def_eq(inner_codomain, &int_const),
                "Codomain should be Int"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", min_info.type_);
    }
}

#[test]
fn test_int_max_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_minmax().unwrap();

    // Int.max : Int → Int → Int
    let max_info = env.get_const(&Name::from_string("Int.max")).unwrap();
    let tc = TypeChecker::new(&env);

    if let ExprKind::Pi(_, ref domain, ref codomain) = &max_info.type_.kind {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "Outer domain should be Int"
        );
        // Inner type should be Int → Int
        if let ExprKind::Pi(_, ref inner_domain, ref inner_codomain) = &codomain.as_ref().kind {
            assert!(
                tc.is_def_eq(inner_domain, &int_const),
                "Inner domain should be Int"
            );
            assert!(
                tc.is_def_eq(inner_codomain, &int_const),
                "Codomain should be Int"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", max_info.type_);
    }
}

#[test]
fn test_int_min_def_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_minmax().unwrap();

    // Int.min_def : ∀ a b : Int, Int.le a b → Eq (Int.min a b) a
    let min_def_info = env.get_const(&Name::from_string("Int.min_def")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type
    if let ExprKind::Pi(_, ref domain, _) = &min_def_info.type_.kind {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "Outer domain should be Int"
        );
    } else {
        panic!("Expected Pi type, got {:?}", min_def_info.type_);
    }
}

#[test]
fn test_int_max_def_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_minmax().unwrap();

    // Int.max_def : ∀ a b : Int, Int.le a b → Eq (Int.max a b) b
    let max_def_info = env.get_const(&Name::from_string("Int.max_def")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type
    if let ExprKind::Pi(_, ref domain, _) = &max_def_info.type_.kind {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "Outer domain should be Int"
        );
    } else {
        panic!("Expected Pi type, got {:?}", max_def_info.type_);
    }
}

#[test]
fn test_int_minmax_dependencies() {
    let mut env = Environment::new();
    env.init_int_minmax().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_int_ord());
    assert!(env.has_eq());
}

// ========================================
// Int.abs properties tests
// ========================================

// ========================================
// FATE Mathlib Stub Tests (#91)
// ========================================

#[test]
fn test_init_prime() {
    let mut env = Environment::new();
    assert!(!env.has_prime());

    env.init_prime().unwrap();
    assert!(env.has_prime());

    // Check Prime constant exists
    let prime_info = env.get_const(&Name::from_string("Prime")).unwrap();
    // Prime : {α : Type u} → α → Prop
    // Should be a Pi type
    assert!(matches!(&prime_info.type_.kind, ExprKind::Pi(_, _, _)));

    // Idempotent
    env.init_prime().unwrap();
    assert!(env.has_prime());
}

#[test]
fn test_init_is_principal_ideal_ring() {
    let mut env = Environment::new();
    assert!(!env.has_is_principal_ideal_ring());

    env.init_is_principal_ideal_ring().unwrap();
    assert!(env.has_is_principal_ideal_ring());

    // Check IsPrincipalIdealRing constant exists
    let pir_info = env
        .get_const(&Name::from_string("IsPrincipalIdealRing"))
        .unwrap();
    // IsPrincipalIdealRing : Type u → Prop
    // Should be a Pi type
    assert!(matches!(&pir_info.type_.kind, ExprKind::Pi(_, _, _)));

    // Idempotent
    env.init_is_principal_ideal_ring().unwrap();
}

#[test]
fn test_init_polynomial() {
    let mut env = Environment::new();
    assert!(!env.has_polynomial());

    env.init_polynomial().unwrap();
    assert!(env.has_polynomial());

    // Check core Polynomial constants exist and have correct type shapes
    // Polynomial : (R : Type u) → Type u
    let poly_info = env
        .get_const(&Name::from_string("Polynomial"))
        .expect("Polynomial should exist");
    assert!(
        matches!(&poly_info.type_.kind, ExprKind::Pi(_, _, _)),
        "Polynomial should be a type constructor"
    );

    // Polynomial.X : {R : Type u} → Polynomial R
    let poly_x = env
        .get_const(&Name::from_string("Polynomial.X"))
        .expect("Polynomial.X should exist");
    assert!(
        matches!(&poly_x.type_.kind, ExprKind::Pi(_, _, _)),
        "Polynomial.X should be a function"
    );

    // Polynomial.C : {R : Type u} → R → Polynomial R
    let poly_c = env
        .get_const(&Name::from_string("Polynomial.C"))
        .expect("Polynomial.C should exist");
    assert!(
        matches!(&poly_c.type_.kind, ExprKind::Pi(_, _, _)),
        "Polynomial.C should be a function"
    );

    // Check Phase 17c polynomial extension stubs (Issue #588)
    // Verify all stubs exist and have Pi types (function signatures)
    let poly_ext_stubs = [
        "Polynomial.natDegree",    // ∀ {R}, Polynomial R → ℕ
        "Polynomial.degree",       // ∀ {R}, Polynomial R → WithBot ℕ
        "Polynomial.leadingCoeff", // ∀ {R}, Polynomial R → R
        "Polynomial.div",          // ∀ {R}, Polynomial R → Polynomial R → Polynomial R
        "Polynomial.mod",          // ∀ {R}, Polynomial R → Polynomial R → Polynomial R
        "Polynomial.divMod",       // ∀ {R}, Polynomial R → Polynomial R → Prod ...
    ];

    for stub in &poly_ext_stubs {
        let info = env
            .get_const(&Name::from_string(stub))
            .unwrap_or_else(|| panic!("Missing polynomial stub: {stub}"));
        assert!(
            matches!(&info.type_.kind, ExprKind::Pi(_, _, _)),
            "Polynomial stub {stub} should have Pi type, got: {:?}",
            info.type_
        );
    }

    // Idempotent
    env.init_polynomial().unwrap();
}

#[test]
fn test_fate_stubs_combined() {
    // Test that all FATE stubs can be initialized together
    let mut env = Environment::new();

    // Initialize all FATE stubs
    env.init_prime().unwrap();
    env.init_is_principal_ideal_ring().unwrap();
    env.init_polynomial().unwrap();

    // Also initialize UFM and Associated which are needed for FATE-X
    env.init_ufm().unwrap();
    env.init_associated().unwrap();

    // All should be available
    assert!(env.has_prime());
    assert!(env.has_is_principal_ideal_ring());
    assert!(env.has_polynomial());
    assert!(env.has_ufm());
    assert!(env.has_associated());

    // Key FATE types should exist
    for s in [
        "Prime",
        "IsPrincipalIdealRing",
        "Polynomial",
        "UniqueFactorizationMonoid",
        "Associated",
    ] {
        assert_const(&env, s);
    }
}

// ===========================================
// Tests for #3222: Rat projection reduction
// ===========================================

/// Test that LE.le @Rat instLERat reduces to Rat.le via projection reduction.
///
/// This is the core of #3222: `LE.le` is defined as
///   `λ {α} [inst : LE α] (a b) => (proj LE 0 inst) a b`
/// so `LE.le @Rat instLERat` should beta+proj reduce to `Rat.le`.
///
/// instLERat is defined as `LE.mk @Rat Rat.le`, so projecting field 0
/// should yield `Rat.le`.
#[test]
fn test_le_le_rat_proj_reduces_to_rat_le() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ord().unwrap();

    let tc = TypeChecker::new(&env);

    // Build: LE.le @Rat instLERat
    // This is: App(App(Const("LE.le", [0]), Rat), instLERat)
    let le_le_rat_instlerat = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            Expr::const_(Name::from_string("Rat"), vec![]),
        ),
        Expr::const_(Name::from_string("instLERat"), vec![]),
    );

    // WHNF should reduce this to Rat.le
    let reduced = tc.whnf(&le_le_rat_instlerat);
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

    // Check def-eq at minimum
    assert!(
        tc.is_def_eq(&reduced, &rat_le),
        "LE.le @Rat instLERat should be def-eq to Rat.le, got: {reduced:?}"
    );
}

/// Test that projection directly on instLERat works:
/// `proj LE 0 instLERat` should reduce to `Rat.le`.
#[test]
fn test_proj_le_0_instlerat_reduces() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_ord().unwrap();

    let tc = TypeChecker::new(&env);

    // Build: Expr::proj("LE", 0, instLERat)
    let proj_expr = Expr::proj(
        Name::from_string("LE"),
        0,
        Expr::const_(Name::from_string("instLERat"), vec![]),
    );

    let reduced = tc.whnf(&proj_expr);
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

    assert!(
        tc.is_def_eq(&reduced, &rat_le),
        "proj LE 0 instLERat should reduce to Rat.le, got: {reduced:?}"
    );
}

/// Test that Preorder.mk can be used to construct instPreorderRat
/// as a proper definition instead of an axiom.
///
/// This constructs:
///   Preorder.mk @Rat instLERat instLTRat Rat.le_refl Rat.le_trans
/// and attempts to type-check it against `Preorder Rat`.
///
/// If this fails, it means projection reduction can't reduce
/// `LE.le @Rat instLERat a a` to `Rat.le a a`, which is the root
/// cause of #3222.
#[test]
fn test_preorder_rat_as_constructed_definition() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_rat_linear_order().unwrap();

    let tc = TypeChecker::new(&env);
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

    // Build: Preorder.mk @Rat instLERat instLTRat Rat.le_refl Rat.le_trans
    let preorder_rat_value = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Preorder.mk"), vec![Level::zero()]),
                        rat_const.clone(),
                    ),
                    Expr::const_(Name::from_string("instLERat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTRat"), vec![]),
            ),
            Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        ),
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
    );

    let expected_type = Expr::app(
        Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
        rat_const,
    );

    // Try to infer the type of the constructed value
    let inferred_type = tc.infer_type(&preorder_rat_value);

    match inferred_type {
        Ok(ty) => {
            // Type-check succeeded - now verify it matches `Preorder Rat`
            assert!(
                tc.is_def_eq(&ty, &expected_type),
                "Inferred type should be Preorder Rat, got: {ty:?}"
            );
        }
        Err(e) => {
            // Expected failure for #3222: report what went wrong
            panic!(
                "#3222 root cause confirmed: cannot type-check \
                 Preorder.mk @Rat instLERat instLTRat Rat.le_refl Rat.le_trans\n\
                 Error: {e:?}"
            );
        }
    }
}

/// Test that instPreorderRat can be registered as a proper Definition
/// instead of an Axiom. This validates the full add_decl path.
///
/// Part of #3222.
#[test]
fn test_inst_preorder_rat_as_definition_registration() {
    use crate::env::Declaration;

    let mut env = Environment::new();
    // init_rat_linear_order sets up everything including instPreorderRat as a
    // Definition. We set up sub-dependencies individually here to test that the
    // Definition registration path works in isolation.
    env.init_rat_ord().unwrap(); // Rat.le, Rat.lt, instLERat, instLTRat
    env.init_preorder().unwrap(); // Preorder typeclass
    env.init_iff().unwrap();
    env.init_and().unwrap();
    env.init_true_false().unwrap();

    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

    // First add the ordering axioms that instPreorderRat needs
    // (these are all Axioms, which is fine — they are mathematical axioms)
    let le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let _eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Rat.le_refl : ∀ a : Rat, Rat.le a a
    {
        let mut bd = decl_builder::EnvDeclBuilder::new();
        let (a_id, a) = bd.fresh_local(rat_const.clone());
        let body = Expr::app(Expr::app(le_const.clone(), a.clone()), a);
        let e = bd.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), body);
        let le_refl_type = bd.finish(e);
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.le_refl"),
            level_params: vec![],
            type_: le_refl_type,
        })
        .unwrap();
    }

    // Rat.le_trans : ∀ a b c : Rat, Rat.le a b → Rat.le b c → Rat.le a c
    {
        let mut bd = decl_builder::EnvDeclBuilder::new();
        let (a_id, a) = bd.fresh_local(rat_const.clone());
        let (b_id, bv) = bd.fresh_local(rat_const.clone());
        let (c_id, c) = bd.fresh_local(rat_const.clone());
        let le_ab = Expr::app(Expr::app(le_const.clone(), a.clone()), bv.clone());
        let le_bc = Expr::app(Expr::app(le_const.clone(), bv), c.clone());
        let le_ac = Expr::app(Expr::app(le_const.clone(), a), c);
        let (hab_id, _) = bd.fresh_local(le_ab.clone());
        let (hbc_id, _) = bd.fresh_local(le_bc.clone());
        let e = bd.mk_pi(hbc_id, BinderInfo::Default, le_bc, le_ac);
        let e = bd.mk_pi(hab_id, BinderInfo::Default, le_ab, e);
        let e = bd.mk_pi(c_id, BinderInfo::Default, rat_const.clone(), e);
        let e = bd.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), e);
        let e = bd.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
        let le_trans_type = bd.finish(e);
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.le_trans"),
            level_params: vec![],
            type_: le_trans_type,
        })
        .unwrap();
    }

    // Now register instPreorderRat as a DEFINITION (not axiom!)
    let inst_type = Expr::app(
        Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
        rat_const.clone(),
    );

    let inst_value = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Preorder.mk"), vec![Level::zero()]),
                        rat_const,
                    ),
                    Expr::const_(Name::from_string("instLERat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTRat"), vec![]),
            ),
            Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        ),
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
    );

    // This is the critical test: can we register instPreorderRat as a Definition?
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("instPreorderRat"),
        level_params: vec![],
        type_: inst_type,
        value: inst_value,
        is_reducible: true,
    });

    assert!(
        result.is_ok(),
        "instPreorderRat should register as a Definition, not an Axiom. Error: {:?}",
        result.err()
    );
}

/// WS-A ATOMIC LIVE SWITCH end-to-end gate: in the LIVE environment (the actual
/// `init_rat_*` chain, NOT the self-contained `init_rat_quotient_poc` validator),
/// EVERY one of the 11 previously-admitted `Rat.*` axioms is a genuine
/// `Declaration::Theorem` that kernel-type-checks and is
/// `ProofQuality::Constructive` (transitive axiom closure ⊆ FOUNDATIONAL via
/// `Quot.sound` / `propext`). This pins the live-flip — the whole point of WS-A.
#[test]
fn test_wsa_eleven_rat_axioms_are_live_constructive_theorems() {
    use super::axiom_audit::ProofQuality;
    use super::ConstantKind;
    use crate::tc::TypeChecker;

    // Drive the full live ordered-field init chain (carrier + ops + order +
    // field instance + ordered-field axioms), which is what every downstream
    // consumer actually links against.
    let mut env = Environment::new();
    env.init_rat_field_inst()
        .expect("init_rat_field_inst (live carrier + ops + field axioms)");
    env.init_rat_linear_order()
        .expect("init_rat_linear_order (Rat.le_antisymm)");
    env.init_rat_ordered_field_axioms()
        .expect("init_rat_ordered_field_axioms (add_le_add_left / le_add_of_nonneg_right)");
    env.init_nn_verify_rat_ordering()
        .expect("init_nn_verify_rat_ordering (Rat.add_neg_self)");

    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in [
        "Rat.zero_mul",
        "Rat.mul_zero",
        "Rat.left_distrib",
        "Rat.right_distrib",
        "Rat.add_left_neg",
        "Rat.add_neg_self",
        "Rat.add_right_cancel",
        "Rat.mul_inv_cancel",
        "Rat.le_antisymm",
        "Rat.add_le_add_left",
        "Rat.le_add_of_nonneg_right",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must be registered in the live env"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a live Declaration::Theorem (WS-A flip), got {:?}",
            info.kind,
        );
        assert!(
            info.value.is_some(),
            "{name} live Theorem must retain a proof value",
        );
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} must kernel-type-check live: {e:?}"));
        let q = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} proof_quality"));
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} must be Constructive in the live env (closure ⊆ FOUNDATIONAL: \
             Quot.sound / propext), got {q:?}",
        );
    }
}
