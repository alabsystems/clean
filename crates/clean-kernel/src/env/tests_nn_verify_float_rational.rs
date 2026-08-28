// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for IEEE 754 float-to-rational bridge module.
//!
//! Part of #3185.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use crate::tc::TypeChecker;

/// Every `Rat.mk (Int.ofNat n) d` in a term, as (numerator, denominator) Debug
/// spellings of the two literals.
///
/// Structural on purpose: the SHAPE comes from the term and only the literal
/// values are compared as text, so this survives any change to how expressions
/// are rendered. The previous form matched whole-expression substrings against
/// `Display`, which broke the moment `Display` improved.
fn rat_literals(e: &Expr) -> Vec<(String, String)> {
    fn lit_debug(e: &Expr) -> Option<String> {
        match e.kind() {
            ExprKind::Lit(Literal::Nat(n)) => Some(format!("{n:?}")),
            _ => None,
        }
    }
    fn head_is(e: &Expr, name: &str) -> bool {
        matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
    }
    let mut out = Vec::new();
    fn walk(e: &Expr, out: &mut Vec<(String, String)>) {
        if let ExprKind::App(f, den) = e.kind() {
            if let ExprKind::App(mk, num_app) = f.kind() {
                if head_is(mk, "Rat.mk") {
                    if let ExprKind::App(of_nat, num) = num_app.kind() {
                        if head_is(of_nat, "Int.ofNat") {
                            if let (Some(n), Some(d)) = (lit_debug(num), lit_debug(den)) {
                                out.push((n, d));
                            }
                        }
                    }
                }
            }
        }
        match e.kind() {
            ExprKind::App(f, a) => {
                walk(f, out);
                walk(a, out);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                walk(t, out);
                walk(b, out);
            }
            ExprKind::Let(_, t, v, b, _) => {
                walk(t, out);
                walk(v, out);
                walk(b, out);
            }
            ExprKind::Proj(_, _, sub) => walk(sub, out),
            _ => {}
        }
    }
    walk(e, &mut out);
    out
}

/// Structural search for a `Nat` literal by value.
///
/// This used to assert `format!("{}", ty).contains("Small(1074)")` — matching
/// `BigNat::Small`'s *Debug* spelling through the `Display` impl. That held only
/// while `Display for Expr` fell back to `Debug`; once it learned Lean notation
/// in 6d1663115 a literal renders as `1074` and the substring vanished. The
/// exponent being pinned is a property of the TERM, so ask the term.
fn mentions_nat_lit(e: &Expr, value: u64) -> bool {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64() == Some(value),
        ExprKind::App(f, a) => mentions_nat_lit(f, value) || mentions_nat_lit(a, value),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            mentions_nat_lit(t, value) || mentions_nat_lit(b, value)
        }
        ExprKind::Let(_, t, v, b, _) => {
            mentions_nat_lit(t, value) || mentions_nat_lit(v, value) || mentions_nat_lit(b, value)
        }
        ExprKind::Proj(_, _, sub) => mentions_nat_lit(sub, value),
        _ => false,
    }
}

/// Structural search for a `Const` by name.
///
/// This shape assertion used to string-match the pretty-printer
/// (`s.contains("And ")`). That broke the moment `Display for Expr` learned
/// Lean notation in 6d1663115 and began printing `∧` — a test asserting a
/// term's SHAPE should not depend on how it is rendered, so it asks the term.
fn mentions_const(e: &Expr, name: &str) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => mentions_const(f, name) || mentions_const(a, name),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            mentions_const(t, name) || mentions_const(b, name)
        }
        ExprKind::Let(_, t, v, b, _) => {
            mentions_const(t, name) || mentions_const(v, name) || mentions_const(b, name)
        }
        ExprKind::Proj(_, _, sub) => mentions_const(sub, name),
        _ => false,
    }
}

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_float_rational()
        .expect("init_nn_verify_float_rational");
    env
}

/// A full-prelude env that also has the float-rational namespace, for the
/// in-kernel reduction tests (the native reducers are wired by the prelude).
fn make_prelude_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_nn_verify_float_rational()
        .expect("init_nn_verify_float_rational");
    env
}

fn mk_float(bits: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Float.mk"), vec![]),
        Expr::nat_lit(bits),
    )
}

/// `Float.toRatExact (Float.mk bits)`.
fn to_rat_exact(bits: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Float.toRatExact"), vec![]),
        mk_float(bits),
    )
}

/// `Float.ulpExact (Float.mk bits)`.
fn ulp_exact(bits: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Float.ulpExact"), vec![]),
        mk_float(bits),
    )
}

/// Native-reduce a `Float.toRatExact`/`Float.ulpExact` application and render
/// the emitted `Rat.mk (Int.ofNat n | Int.negSucc n) den` as a string.
fn reduce_and_show(env: &Environment, e: &Expr) -> String {
    let tc = TypeChecker::with_mode(env, env.mode());
    let reduced = tc
        .reduce_native_for_test(e)
        .expect("native reducer should fire");
    let args = reduced.get_app_args();
    let num = match args
        .first()
        .map(|n| (n.get_app_fn().kind(), n.get_app_args()))
    {
        Some((ExprKind::Const(name, _), nargs)) => {
            let mag = match nargs.first().map(|a| a.kind()) {
                Some(ExprKind::Lit(Literal::Nat(n))) => format!("{n:?}"),
                other => format!("{other:?}"),
            };
            format!("{}({mag})", name)
        }
        other => format!("{other:?}"),
    };
    let den = match args.get(1).map(|d| d.kind()) {
        Some(ExprKind::Lit(Literal::Nat(n))) => format!("{n:?}"),
        other => format!("{other:?}"),
    };
    format!("Rat.mk {num} {den}")
}

// === Definition registration tests ===

#[test]
fn test_float_to_rational_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.float_to_rational"
        ))
        .is_some());
}

#[test]
fn test_ulp_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.FloatRational.ulp"))
        .is_some());
}

#[test]
fn test_rounding_error_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.FloatRational.rounding_error"))
        .is_some());
}

#[test]
fn test_interval_float_rational_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.interval_float_rational"
        ))
        .is_some());
}

#[test]
fn test_accumulated_error_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.accumulated_error"
        ))
        .is_some());
}

// === Axiom/theorem registration tests ===

#[test]
fn test_float_to_rational_exact_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.float_to_rational_exact"
        ))
        .is_some());
}

#[test]
fn test_rounding_error_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.rounding_error_bound"
        ))
        .is_some());
}

#[test]
fn test_interval_contains_real_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.interval_contains_real"
        ))
        .is_some());
}

#[test]
fn test_matmul_error_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.matmul_error_bound"
        ))
        .is_some());
}

#[test]
fn test_ibp_float_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.FloatRational.ibp_float_sound"))
        .is_some());
}

#[test]
fn test_error_propagation_linear_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.error_propagation_linear"
        ))
        .is_some());
}

// === Type checking tests ===

#[test]
fn test_float_to_rational_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.float_to_rational"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer float_to_rational type");
    // Float -> Rat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ulp_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.FloatRational.ulp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ulp type");
    // Float -> Rat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_rounding_error_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.rounding_error"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer rounding_error type");
    // Rat -> Float -> Rat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interval_float_rational_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.interval_float_rational"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer interval_float_rational type");
    // Float -> Float -> Rat -> Rat -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_accumulated_error_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.accumulated_error"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer accumulated_error type");
    // Nat -> Rat -> Rat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_float_to_rational_exact_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.float_to_rational_exact"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer float_to_rational_exact type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_rounding_error_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.rounding_error_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer rounding_error_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_matmul_error_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.matmul_error_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer matmul_error_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ibp_float_sound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.ibp_float_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ibp_float_sound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_error_propagation_linear_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.FloatRational.error_propagation_linear"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer error_propagation_linear type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// === Structural tests ===

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_float_rational().expect("first init");
    env.init_nn_verify_float_rational().expect("second init");
}

#[test]
fn test_nn_verify_float_rational_naming_convention() {
    let env = make_env();
    let expected_names = [
        "NNVerify.FloatRational.float_to_rational",
        "NNVerify.FloatRational.ulp",
        "NNVerify.FloatRational.rounding_error",
        "NNVerify.FloatRational.interval_float_rational",
        "NNVerify.FloatRational.accumulated_error",
        "NNVerify.FloatRational.float_to_rational_exact",
        "NNVerify.FloatRational.rounding_error_bound",
        "NNVerify.FloatRational.interval_contains_real",
        "NNVerify.FloatRational.matmul_error_bound",
        "NNVerify.FloatRational.ibp_float_sound",
        "NNVerify.FloatRational.error_propagation_linear",
    ];
    for name in &expected_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

#[test]
fn test_definitions_are_definitions() {
    let env = make_env();
    // interval_float_rational is the only Definition (has value)
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.interval_float_rational",
        ))
        .expect("should exist");
    assert_eq!(info.kind, ConstantKind::Definition);
    assert!(info.value.is_some(), "definition should have a value");
}

#[test]
fn test_axioms_are_axioms() {
    let env = make_env();
    let axiom_names = [
        "NNVerify.FloatRational.float_to_rational",
        "NNVerify.FloatRational.ulp",
        "NNVerify.FloatRational.rounding_error",
        "NNVerify.FloatRational.accumulated_error",
        "NNVerify.FloatRational.float_to_rational_exact",
        "NNVerify.FloatRational.rounding_error_bound",
        "NNVerify.FloatRational.interval_contains_real",
        "NNVerify.FloatRational.matmul_error_bound",
        "NNVerify.FloatRational.ibp_float_sound",
        "NNVerify.FloatRational.error_propagation_linear",
    ];
    for name in &axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "{} should be an Axiom, got {:?}",
            name,
            info.kind,
        );
    }
}

/// Total count: 5 definitions + 6 axioms + 1 discharge theorem
/// (`float_to_rat_exact_discharge_01`) = 12 declarations under the
/// `NNVerify.FloatRational.` prefix. (The `Float.toRatExact` / `Float.ulpExact`
/// constants live under the `Float.` prefix, so they are not counted here.)
#[test]
fn test_total_declaration_count() {
    let env = make_env();
    let prefix = "NNVerify.FloatRational.";
    let count = env
        .constants()
        .filter(|c| c.name.to_string().starts_with(prefix))
        .count();
    assert_eq!(count, 12, "expected 12 float-rational declarations");
}

// === Stage A: native exact float→rational decomposition ===

/// `Float.toRatExact` / `Float.ulpExact` are registered as `Opaque` constants
/// (NOT `Axiom`): their computational content is the native reducer, and they
/// must add no axiom debt.
#[test]
fn test_float_exact_decomp_constants_are_opaque() {
    let env = make_env();
    for name in ["Float.toRatExact", "Float.ulpExact"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} must be Opaque (native-reducer-backed), not {:?}",
            info.kind
        );
    }
}

/// `Float.toRatExact` reduces in-kernel to the EXACT dyadic rational for each
/// of the IEEE-754 regimes. The expected strings are the literal `Rat.mk`
/// normal forms the kernel produces. (Denominators that exceed `u64` print as
/// `Big([...])` limbs.)
#[test]
fn test_to_rat_exact_reduces_all_regimes() {
    let env = make_prelude_env();

    // Normal: 1.0 = 2^52 / 2^52.
    assert_eq!(
        reduce_and_show(&env, &to_rat_exact(1.0f64.to_bits())),
        "Rat.mk Int.ofNat(Small(4503599627370496)) Small(4503599627370496)"
    );

    // Normal: 0.1 = 7205759403792794 / 2^56  (the exact stored value).
    assert_eq!(
        reduce_and_show(&env, &to_rat_exact(0.1f64.to_bits())),
        "Rat.mk Int.ofNat(Small(7205759403792794)) Small(72057594037927936)"
    );

    // Power-of-two boundary: 2.0 = 2^52 · 2^-51 = 2^52/1 shifted... emitted as
    // num << 1 over denominator 1 (exp = -51 < 0 so den = 2^51).
    assert_eq!(
        reduce_and_show(&env, &to_rat_exact(2.0f64.to_bits())),
        "Rat.mk Int.ofNat(Small(4503599627370496)) Small(2251799813685248)" // 2^52 / 2^51
    );

    // Signed zero: BOTH +0.0 and -0.0 convert to the rational 0.
    assert_eq!(
        reduce_and_show(&env, &to_rat_exact(0.0f64.to_bits())),
        "Rat.mk Int.ofNat(Small(0)) Small(1)"
    );
    assert_eq!(
        reduce_and_show(&env, &to_rat_exact((-0.0f64).to_bits())),
        "Rat.mk Int.ofNat(Small(0)) Small(1)"
    );

    // Subnormal: f64::from_bits(1) = 2^-1074 = 1 / 2^1074 (denominator is Big).
    let sub = reduce_and_show(&env, &to_rat_exact(1u64));
    assert!(
        sub.starts_with("Rat.mk Int.ofNat(Small(1)) Big("),
        "smallest subnormal must be 1 / 2^1074 with a Big denominator; got {sub}"
    );
}

/// `Float.ulpExact` reduces in-kernel, and the denormal ULP FLOOR holds: every
/// subnormal AND zero floors at `2^-1074`. This is the floor whose ABSENCE let
/// ny's softmax underflow through.
#[test]
fn test_ulp_exact_denormal_floor_reduces() {
    let env = make_prelude_env();

    // Normal: ulp(1.0) = 2^-52 = 1 / 2^52.
    assert_eq!(
        reduce_and_show(&env, &ulp_exact(1.0f64.to_bits())),
        "Rat.mk Int.ofNat(Small(1)) Small(4503599627370496)" // 1 / 2^52
    );

    // The FLOOR: smallest subnormal, largest subnormal, and BOTH signed zeros
    // all give ulp = 2^-1074 = 1 / 2^1074 (Big denominator).
    for (label, bits) in [
        ("smallest subnormal", 1u64),
        ("largest subnormal", 0x000F_FFFF_FFFF_FFFF_u64),
        ("+0.0", 0.0f64.to_bits()),
        ("-0.0", (-0.0f64).to_bits()),
    ] {
        let s = reduce_and_show(&env, &ulp_exact(bits));
        assert!(
            s.starts_with("Rat.mk Int.ofNat(Small(1)) Big("),
            "ulp floor for {label} must be 1 / 2^1074 (Big den); got {s}"
        );
    }
}

/// `Float.toRatExact (Float.mk 0.1)` is *definitionally equal* in the kernel to
/// the exact rational `Rat.mk (Int.ofNat 7205759403792794) (2^56)` — i.e. the
/// kernel itself confirms the computation (this is what makes the discharge
/// theorem's `Eq.refl` proof check).
#[test]
fn test_to_rat_exact_is_def_eq_to_exact_rational() {
    let env = make_prelude_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let lhs = to_rat_exact(0.1f64.to_bits());
    let rhs = Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [
            Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::nat_lit(7205759403792794),
            ),
            Expr::nat_lit(72057594037927936), // 2^56
        ],
    );
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "kernel must reduce Float.toRatExact(mk 0.1) to the exact 0.1 rational"
    );
    // And a sanity NON-equality: it must NOT be def-eq to a different rational
    // (e.g. with denominator 2^55), proving the check is discriminating.
    let wrong = Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [
            Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::nat_lit(7205759403792794),
            ),
            Expr::nat_lit(36028797018963968), // 2^55, half the true denominator
        ],
    );
    assert!(
        !tc.is_def_eq(&lhs, &wrong),
        "must distinguish the true 0.1 rational from a wrong one"
    );
}

/// The discharge theorem `float_to_rat_exact_discharge_01` is a real
/// `Theorem` (not an Axiom), type-checks, and has an EMPTY non-foundational
/// axiom closure — the per-float exactness fact is now CHECKED, not asserted.
#[test]
fn test_discharge_01_is_checked_theorem_with_empty_closure() {
    let env = make_env();
    let name = Name::from_string("NNVerify.FloatRational.float_to_rat_exact_discharge_01");

    let info = env
        .get_const(&name)
        .expect("discharge theorem should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "discharge must be a Theorem proved by computation, not an Axiom"
    );

    // It type-checks against its stated Eq type.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let e = Expr::const_(name.clone(), vec![]);
    let _ = tc
        .infer_type(&e)
        .expect("discharge theorem must type-check");

    // Non-foundational axiom closure is empty: no `sorry`, no domain axioms.
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps available for discharge theorem");
    let deps_str: std::collections::HashSet<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        !deps_str.contains("sorry") && !deps_str.contains("sorryAx"),
        "discharge must not depend on sorry; got {deps_str:?}"
    );
    assert!(
        deps_str.is_empty(),
        "discharge non-foundational closure must be empty; got {deps_str:?}"
    );
}

// ===== Stage B: the GENERAL half-ulp rounding lemma (incl. denormals) =====

/// The universal `∀ (e N)` half-ulp bound and the named binary64 DENORMAL
/// instance are registered as `Theorem`s, type-check, and rest on an EMPTY
/// non-foundational axiom closure (sorry-free, no hidden domain axiom). The
/// universal statement keeps `Nat.pow 2 e` SYMBOLIC (holds for ALL exponents,
/// so the bound binds in the normal AND the floored-ulp denormal regime).
#[test]
fn test_half_ulp_universal_and_denormal_axiom_free() {
    let env = make_prelude_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for n in [
        "NNVerify.FloatRational.rounding_error_le_half_ulp",
        "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
    ] {
        let name = Name::from_string(n);
        let info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{n} missing"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{n} must be a Theorem");
        let ty = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .unwrap_or_else(|e| panic!("{n} must type-check: {e:?}"));
        let s = format!("{ty}");
        // Two-sided half-step bound shape over the round + power-of-two grid.
        assert!(mentions_const(&ty, "And"), "{n}: missing And: {s}");
        assert!(
            s.contains("Nat.roundHalfEvenMod"),
            "{n}: missing round: {s}"
        );
        assert!(
            s.contains("Nat.pow"),
            "{n}: grid spacing must be Nat.pow: {s}"
        );
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("{n}: axiom_deps None"));
        assert!(
            deps.is_empty(),
            "{n} non-foundational closure must be empty; got {deps:?}"
        );
    }
    // The universal statement must keep the exponent SYMBOLIC (a binder `n`
    // surviving inside `Nat.pow 2 n`), i.e. it is genuinely `∀ e`.
    let univ = env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.rounding_error_le_half_ulp",
        ))
        .unwrap();
    let s = format!("{}", univ.type_);
    assert!(
        s.starts_with("(n : Nat) -> (n1 : Nat) ->"),
        "universal bound must be ∀ e N: {s}"
    );
    // The denormal instance pins the binary64 floored-ulp exponent 1074.
    let den = env
        .get_const(&Name::from_string(
            "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
        ))
        .unwrap();
    assert!(
        mentions_nat_lit(&den.type_, 1074),
        "denormal instance must pin the floored exponent 1074: {}",
        den.type_
    );
}

/// `Rat.roundToNearestEven` is an `Opaque` (native-reducer-backed) constant, and
/// reduces in-kernel to the ties-to-even rounded value for each regime.
#[test]
fn test_round_to_nearest_even_reduces_all_regimes() {
    let env = make_prelude_env();
    let info = env
        .get_const(&Name::from_string("Rat.roundToNearestEven"))
        .expect("Rat.roundToNearestEven registered");
    assert_eq!(info.kind, ConstantKind::Opaque);

    let round = |q: Expr, v: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.roundToNearestEven"), vec![]),
            [q, v],
        )
    };
    let mk = |num: u64, den: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    Expr::nat_lit(num),
                ),
                Expr::nat_lit(den),
            ],
        )
    };

    // NORMAL: round 5/16 onto grid 1/4 → 4/16 (= 1/4).
    assert_eq!(
        reduce_and_show(&env, &round(mk(5, 16), mk(1, 4))),
        "Rat.mk Int.ofNat(Small(4)) Small(16)"
    );
    // TIE: round 3/4 onto grid 1/2 → 4/4 (= 1), ties-to-even up to even index.
    assert_eq!(
        reduce_and_show(&env, &round(mk(3, 4), mk(1, 2))),
        "Rat.mk Int.ofNat(Small(4)) Small(4)"
    );
    // EXACT: round 3/4 onto grid 1/4 → 3/4 unchanged (error 0).
    assert_eq!(
        reduce_and_show(&env, &round(mk(3, 4), mk(1, 4))),
        "Rat.mk Int.ofNat(Small(3)) Small(4)"
    );
    // SUBNORMAL-style (floored uniform grid 1/1024): round 5/2048 → 4/2048,
    // ties-to-even DOWN to the even index. The floored ulp binds.
    assert_eq!(
        reduce_and_show(&env, &round(mk(5, 2048), mk(1, 1024))),
        "Rat.mk Int.ofNat(Small(4)) Small(2048)"
    );
}

/// The four per-constant discharges of `rounding_error_bound` — normal,
/// subnormal (floored ulp), tie (ties-to-even), and exact (error 0) — are
/// kernel-checked `Theorem`s (NOT axioms), with EMPTY non-foundational axiom
/// closures. Each pairs (a) an `Eq.refl` discharge that the native
/// `Rat.roundToNearestEven` REDUCES `q` to the literal rounded value, with
/// (b) the half-ulp BOUND `2·|round q − q| ≤ ulp` on that value, proved by the
/// concrete non-negativity witness `Int.NonNeg.mk`. Together they REDUCE the
/// bound in-kernel for all four cases.
#[test]
fn test_rounding_error_bound_discharges_axiom_free() {
    let env = make_prelude_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    // The subnormal case is now discharged at the TRUE binary64 floored-ulp
    // scale `2^-1074` (denominator `2^1074`, a 17-limb `Big` bignat): q =
    // 5·2^-1075 = 2.5 floored-ulps, ties-to-even DOWN to grid index 2, error =
    // ulp/2 EXACTLY → both LHS (`2·|round−q|`) and RHS (`ulp`) are `1/2^1074`.
    // `2^1074`'s top (and only nonzero) limb is `1125899906842624` (= 2^50,
    // since 1074 = 16·64 + 50), so the den is `Big([...0, 1125899906842624])`.
    // This LITERAL reduces in-kernel (the `Nat.pred` + arbitrary-precision `Int`
    // reducers close the Rat-blowup wall) — `tc.infer_type` below type-checks it.
    // (tag, LHS numerator/denominator, RHS numerator/denominator) as the
    // `Rat.mk (Int.ofNat n) d` values the bound must pin. The denominator is a
    // FRAGMENT of the literal's Debug spelling so the 17-limb subnormal `Big`
    // can be matched by its top limb without writing 2^1074 out.
    //
    // This was a table of whole-expression substrings
    // (`"Nat(Small(2))) Nat(Small(16))"`) matched against `format!("{}", ty)`.
    // Those markers encoded the OLD `Display`, a hybrid that printed
    // applications Lean-style but literals in Debug spelling. Once Display
    // learned real Lean notation in 6d1663115 the markers could match nothing —
    // and `{:?}` does not restore them either, because Debug separates
    // application arguments with `, ` where the old Display used a space. The
    // values being pinned are properties of the TERM, so read them off it.
    let cases = [
        (
            "normal",
            ("Small(2)", "Small(16)"),
            ("Small(1)", "Small(4)"),
        ),
        (
            "subnormal",
            ("Small(1)", "1125899906842624"),
            ("Small(1)", "1125899906842624"),
        ),
        ("tie", ("Small(2)", "Small(4)"), ("Small(1)", "Small(2)")),
        ("exact", ("Small(0)", "Small(4)"), ("Small(1)", "Small(4)")),
    ];
    for (tag, lhs_marker, rhs_marker) in cases {
        let bound = Name::from_string(&format!(
            "NNVerify.FloatRational.rounding_error_bound_discharge_{tag}"
        ));
        let round_eq = Name::from_string(&format!("NNVerify.FloatRational.round_discharge_{tag}"));
        for name in [&bound, &round_eq] {
            let info = env
                .get_const(name)
                .unwrap_or_else(|| panic!("{name:?} missing"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name:?} must be a Theorem"
            );
            let _ = tc
                .infer_type(&Expr::const_(name.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name:?} must type-check: {e:?}"));
            let deps = env
                .axiom_deps(name)
                .unwrap_or_else(|| panic!("{name:?}: axiom_deps None"));
            let ds: std::collections::HashSet<String> =
                deps.iter().map(|x| x.to_string()).collect();
            assert!(
                !ds.contains("sorry") && !ds.contains("sorryAx"),
                "{name:?} must not depend on sorry; got {ds:?}"
            );
            assert!(ds.is_empty(), "{name:?} closure must be empty; got {ds:?}");
        }
        // The bound's stated type is `LHS ≤ RHS` with the expected operands.
        // These markers are `BigNat`/`Literal` DEBUG spellings
        // (`Nat(Small(16))`, `Nat(Big(`). They matched only while
        // `Display for Expr` fell back to `Debug`; since 6d1663115 Display
        // speaks Lean notation and a literal renders as `16`. Ask for `{:?}`
        // explicitly, which is what this table always meant — rather than
        // rewriting the exact rational values it pins.
        let bty = &env.get_const(&bound).unwrap().type_;
        let found = rat_literals(bty);
        for (side, (num, den)) in [("LHS", lhs_marker), ("RHS", rhs_marker)] {
            assert!(
                found.iter().any(|(n, d)| n == num && d.contains(den)),
                "{tag}: bound {side} Rat.mk {num}/{den} not among {found:?}"
            );
        }
    }
}
