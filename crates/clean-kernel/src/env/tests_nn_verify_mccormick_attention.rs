// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C005: McCormick attention tightness novel kernel theorem.
//!
//! All tests use `run_with_stack(HUGE_STACK)` because `Environment::new()`
//! overflows default 8 MB stack (#1455).  Prerequisites are stubbed via
//! `add_decl_unchecked` with init flags set directly to bypass the deep
//! WHNF normalization chain.  Part of #3150.

use crate::env::types::ConstantKind;
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::test_utils::run_with_stack;
use std::process::Command;

/// 256 MB stack -- `Environment::new()` alone requires >64 MB in debug mode.
const HUGE_STACK: usize = 256 * 1024 * 1024;

/// Helper: run test body on a thread with sufficient stack.
fn run<F: FnOnce() + Send + 'static>(f: F) {
    run_with_stack(HUGE_STACK, f);
}

// ========================================================================
// Stub registration helpers (split from make_env_with_stubs for size)
// ========================================================================

/// Register the `Rat` type and arithmetic operations as unchecked stubs.
fn stub_rat_arithmetic(env: &mut Environment) {
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let sort_one = Expr::sort(Level::succ(Level::zero()));

    // Rat : Type (Sort 1)
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("Rat"),
        level_params: vec![],
        type_: sort_one,
    });

    // Binary Rat ops: Rat -> Rat -> Rat
    let rat_binop = Expr::pi(
        BinderInfo::Default,
        rat.clone(),
        Expr::pi(BinderInfo::Default, rat.clone(), rat.clone()),
    );
    for op in &["Rat.mul", "Rat.sub", "Rat.add", "Rat.div"] {
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string(op),
            level_params: vec![],
            type_: rat_binop.clone(),
        });
    }

    // Unary: Rat.abs, Rat.neg : Rat -> Rat
    let rat_unary = Expr::pi(BinderInfo::Default, rat.clone(), rat.clone());
    for op in &["Rat.abs", "Rat.neg"] {
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string(op),
            level_params: vec![],
            type_: rat_unary.clone(),
        });
    }

    // Rat constants: Rat.zero, Rat.one : Rat
    for c in &["Rat.zero", "Rat.one"] {
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string(c),
            level_params: vec![],
            type_: rat.clone(),
        });
    }
}

/// Register comparison/ordering stubs: LE.le, instLERat, Rat.le, Rat.lt.
fn stub_comparison_ops(env: &mut Environment) {
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let prop = Expr::prop();
    let sort_one = Expr::sort(Level::succ(Level::zero()));

    // LE.le stub (universe-polymorphic, simplified for Rat usage)
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("LE.le"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            sort_one.clone(),
            Expr::pi(
                BinderInfo::InstImplicit,
                sort_one.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    rat.clone(),
                    Expr::pi(BinderInfo::Default, rat.clone(), prop.clone()),
                ),
            ),
        ),
    });

    // instLERat : LE Rat
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("instLERat"),
        level_params: vec![],
        type_: sort_one,
    });

    // Rat.le, Rat.lt : Rat -> Rat -> Prop
    for n in &["Rat.le", "Rat.lt"] {
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                rat.clone(),
                Expr::pi(BinderInfo::Default, rat.clone(), prop.clone()),
            ),
        });
    }
}

/// Register equality stubs: Eq, Eq.refl.
fn stub_eq_ops(env: &mut Environment) {
    let prop = Expr::prop();
    let sort_one = Expr::sort(Level::succ(Level::zero()));

    // Eq : {u} -> (a : Sort u) -> a -> a -> Prop
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            sort_one.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop),
            ),
        ),
    });

    // Eq.refl : {α : Sort u} → (a : α) → @Eq α a a
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            sort_one,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    });
}

/// Register conjunction stubs: And, And.intro.
fn stub_and_ops(env: &mut Environment) {
    let prop = Expr::prop();

    // And : Prop -> Prop -> Prop
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("And"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            prop.clone(),
            Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
        ),
    });

    // And.intro : {a b : Prop} -> a -> b -> And a b
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("And.intro"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            prop.clone(),
            Expr::pi(
                BinderInfo::Implicit,
                prop.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1),
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("And"), vec![]),
                                Expr::bvar(3),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    });
}

/// Register base McCormick stubs: gap, envelope_lower/upper, mccormick_sound.
fn stub_mccormick_base(env: &mut Environment) {
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);

    // NNVerify.McCormick.gap : Rat -> Rat -> Rat -> Rat -> Rat
    let rat4_to_rat = Expr::pi(
        BinderInfo::Default,
        rat.clone(),
        Expr::pi(
            BinderInfo::Default,
            rat.clone(),
            Expr::pi(
                BinderInfo::Default,
                rat.clone(),
                Expr::pi(BinderInfo::Default, rat.clone(), rat.clone()),
            ),
        ),
    );
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("NNVerify.McCormick.gap"),
        level_params: vec![],
        type_: rat4_to_rat.clone(),
        value: rat.clone(), // stub value
        is_reducible: true,
    });

    for name in &[
        "NNVerify.McCormick.envelope_lower",
        "NNVerify.McCormick.envelope_upper",
    ] {
        env.add_decl_unchecked(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: rat4_to_rat.clone(),
            value: rat.clone(),
            is_reducible: true,
        });
    }
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("NNVerify.McCormick.mccormick_sound"),
        level_params: vec![],
        type_: Expr::prop(),
    });
}

/// Ensure the `sorry` axiom is registered for opaque declaration support.
/// Environment::new() already registers sorry, so this is a no-op guard.
fn stub_sorry(env: &mut Environment) {
    if env.get_const(&Name::from_string("sorry")).is_some() {
        return;
    }
    let sort_one = Expr::sort(Level::succ(Level::zero()));

    // sorry.{u} : {α : Sort u} → α
    // Simplified stub: sorry : {α : Type} → α
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("sorry"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(BinderInfo::Implicit, sort_one, Expr::bvar(0)),
    });
}

fn opaque_value(env: &Environment, name: &str) -> Expr {
    let ci = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "{name} should be an Opaque before inspecting its sorry body",
    );
    ci.value
        .clone()
        .unwrap_or_else(|| panic!("{name} should carry an opaque value"))
}

fn peel_lams(expr: &Expr) -> &Expr {
    let mut curr = expr;
    while let ExprKind::Lam(_, _, body) = curr.kind() {
        curr = body;
    }
    curr
}

fn assert_canonical_synthetic_sorry_ax_body(name: &str, value: &Expr) {
    let body = peel_lams(value);
    assert!(
        body.is_synthetic_sorry(),
        "{name} opaque body should be canonical synthetic sorryAx, got {body:?}",
    );
    assert!(
        !body.is_non_synthetic_sorry(),
        "{name} opaque body should not be legacy bare sorry or explicit sorryAx",
    );

    match body.get_app_fn().kind() {
        ExprKind::Const(head, _) => assert_eq!(
            *head,
            Name::from_string("sorryAx"),
            "{name} opaque body should be headed by sorryAx, got {head:?}",
        ),
        other => panic!("{name} opaque body should be a sorryAx application, got {other:?}"),
    }

    let args = body.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "{name} synthetic sorryAx body should have goal and synthetic-flag args",
    );
    match args[1].kind() {
        ExprKind::Const(flag, _) => assert!(
            *flag == Name::from_string("Bool.true") || *flag == Name::from_string("true"),
            "{name} synthetic sorryAx flag should be true, got {flag:?}",
        ),
        other => panic!("{name} synthetic sorryAx flag should be true, got {other:?}"),
    }
}

/// Build a complete environment with stubs, bypassing the deep init chain.
///
/// Shared with sibling `tests_nn_verify_mccormick_attention_demasquerade_3594`
/// so the dedicated demasquerade pin file can reuse the stub infrastructure
/// instead of duplicating ~200 lines of base + arithmetic stubs.
pub(super) fn make_env_with_stubs() -> Environment {
    let mut env = Environment::new();

    stub_rat_arithmetic(&mut env);
    stub_comparison_ops(&mut env);
    stub_eq_ops(&mut env);
    stub_and_ops(&mut env);
    stub_mccormick_base(&mut env);
    stub_sorry(&mut env);

    // Set init flags to skip the real init chain
    env.nn_verify_mccormick_init = true;
    env.rat_abs_init = true;
    env.and_init = true;
    env.eq_init = true;
    env.rat_arith_init = true;
    env.rat_ord_init = true;

    env.init_nn_verify_mccormick_attention()
        .expect("init_nn_verify_mccormick_attention with stubs");

    env
}

// ========================================================================
// Registration tests
// ========================================================================

#[test]
fn test_shared_input_lower_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(
            env.get_const(&Name::from_string("NNVerify.McCormick.shared_input_lower"))
                .is_some(),
            "shared_input_lower should be registered",
        );
    });
}

#[test]
fn test_shared_input_upper_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(env
            .get_const(&Name::from_string("NNVerify.McCormick.shared_input_upper"))
            .is_some(),);
    });
}

#[test]
fn test_shared_input_width_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(env
            .get_const(&Name::from_string("NNVerify.McCormick.shared_input_width"))
            .is_some(),);
    });
}

#[test]
fn test_shared_input_width_eq_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(env
            .get_const(&Name::from_string(
                "NNVerify.McCormick.shared_input_width_eq"
            ))
            .is_some(),);
    });
}

#[test]
fn test_shared_input_gap_eq_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(env
            .get_const(&Name::from_string("NNVerify.McCormick.shared_input_gap_eq"))
            .is_some(),);
    });
}

#[test]
fn test_shared_input_normalized_le_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(env
            .get_const(&Name::from_string(
                "NNVerify.McCormick.shared_input_normalized_le"
            ))
            .is_some(),);
    });
}

#[test]
fn test_attention_tightness_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(
            env.get_const(&Name::from_string("NNVerify.McCormick.attention_tightness"))
                .is_some(),
            "C005 main theorem should be registered",
        );
    });
}

#[test]
fn test_attention_gap_linear_registered() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(env
            .get_const(&Name::from_string(
                "NNVerify.McCormick.attention_gap_linear_in_eps"
            ))
            .is_some(),);
    });
}

// ========================================================================
// Structural verification tests
// ========================================================================

#[test]
fn test_attention_tightness_is_theorem_not_axiom() {
    run(|| {
        let env = make_env_with_stubs();
        let ci = env
            .get_const(&Name::from_string("NNVerify.McCormick.attention_tightness"))
            .expect("attention_tightness should exist");
        assert!(
            ci.value.is_some(),
            "C005 attention_tightness should be a Theorem (has proof term), not an Axiom",
        );
    });
}

#[test]
fn test_definitions_have_values() {
    run(|| {
        let env = make_env_with_stubs();
        // `shared_input_width` was co-demoted from reducible Definition to
        // Opaque in #3594 Branch A; it still has a value but is no longer a
        // Definition. See `tests_nn_verify_mccormick_attention_demasquerade_3594`
        // for the dedicated Opaque pin.
        for name in &[
            "NNVerify.McCormick.shared_input_lower",
            "NNVerify.McCormick.shared_input_upper",
        ] {
            let ci = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{} should exist", name));
            assert!(
                ci.value.is_some(),
                "{} should be a Definition (has value)",
                name
            );
        }
    });
}

#[test]
fn test_former_axioms_are_now_opaques_with_values() {
    run(|| {
        let env = make_env_with_stubs();
        for name in &[
            "NNVerify.McCormick.shared_input_gap_eq",
            "NNVerify.McCormick.shared_input_normalized_le",
            "NNVerify.McCormick.attention_gap_linear_in_eps",
        ] {
            let ci = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{} should exist", name));
            assert!(
                ci.value.is_some(),
                "{} should be an Opaque (has value), not an Axiom (#3381)",
                name,
            );
        }
    });
}

#[test]
fn test_opaque_values_use_canonical_synthetic_sorry_ax() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(
            env.get_const(&Name::from_string("sorryAx")).is_some(),
            "C005 init should run after Bool/sorryAx initialization",
        );

        for name in [
            "NNVerify.McCormick.shared_input_gap_eq",
            "NNVerify.McCormick.shared_input_normalized_le",
            "NNVerify.McCormick.attention_gap_linear_in_eps",
        ] {
            let value = opaque_value(&env, name);
            assert_canonical_synthetic_sorry_ax_body(name, &value);
        }
    });
}

#[test]
fn deny_sorry_child_mccormick_attention_init() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("mccormick_attention_init") {
        return;
    }
    run(|| {
        let _ = make_env_with_stubs();
    });
}

#[test]
fn test_deny_sorry_blocks_mccormick_attention_init() {
    let exe = std::env::current_exe().expect("cannot get current test exe path");
    let output = Command::new(&exe)
        .env("DENY_SORRY", "1")
        .env("DENY_SORRY_GATE_CHILD", "mccormick_attention_init")
        .arg("deny_sorry_child_mccormick_attention_init")
        .arg("--test-threads=1")
        .arg("--nocapture")
        .output()
        .expect("failed to exec DENY_SORRY child process");

    assert!(
        !output.status.success(),
        "init_nn_verify_mccormick_attention should panic under DENY_SORRY=1.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("DENY_SORRY mode enabled"),
        "panic should come from DENY_SORRY sorry creation guard, got stderr:\n{stderr}",
    );
}

/// `shared_input_width_eq` is a local-evidence theorem. Its companion
/// carrier remains opaque so this does not re-open the old Eq.refl
/// alias-collapse proof.
#[test]
fn test_width_eq_is_hypothesis_wrapped_theorem() {
    run(|| {
        let env = make_env_with_stubs();
        let ci = env
            .get_const(&Name::from_string(
                "NNVerify.McCormick.shared_input_width_eq",
            ))
            .expect("shared_input_width_eq should exist");
        assert_eq!(
            ci.kind,
            ConstantKind::Theorem,
            "shared_input_width_eq should be a local-evidence theorem, got {:?}",
            ci.kind,
        );
        assert!(
            ci.value.is_some(),
            "shared_input_width_eq theorem must carry the local-evidence proof value",
        );
    });
}

// ========================================================================
// Idempotency test
// ========================================================================

#[test]
fn test_idempotent() {
    run(|| {
        let mut env = make_env_with_stubs();
        env.init_nn_verify_mccormick_attention()
            .expect("second init should be idempotent");
    });
}

// ========================================================================
// Naming convention test
// ========================================================================

#[test]
fn test_naming_convention() {
    run(|| {
        let env = make_env_with_stubs();
        let names = [
            "NNVerify.McCormick.shared_input_lower",
            "NNVerify.McCormick.shared_input_upper",
            "NNVerify.McCormick.shared_input_width",
            "NNVerify.McCormick.shared_input_width_eq",
            "NNVerify.McCormick.shared_input_gap_eq",
            "NNVerify.McCormick.shared_input_normalized_le",
            "NNVerify.McCormick.attention_tightness",
            "NNVerify.McCormick.attention_gap_linear_in_eps",
        ];
        for name in &names {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{} should be registered",
                name,
            );
            assert!(
                name.starts_with("NNVerify.McCormick."),
                "C005 name must use NNVerify.McCormick. prefix: {}",
                name,
            );
        }
    });
}

// ========================================================================
// Backward compatibility
// ========================================================================

#[test]
fn test_base_mccormick_still_accessible() {
    run(|| {
        let env = make_env_with_stubs();
        assert!(
            env.get_const(&Name::from_string("NNVerify.McCormick.envelope_lower"))
                .is_some(),
            "envelope_lower should be accessible",
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.McCormick.gap"))
                .is_some(),
            "gap should be accessible",
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.McCormick.mccormick_sound"))
                .is_some(),
            "mccormick_sound should be accessible",
        );
    });
}

// ========================================================================
// Count test: all 8 C005 declarations
// ========================================================================

#[test]
fn test_all_c005_declarations_count() {
    run(|| {
        let env = make_env_with_stubs();
        let c005_names = [
            "NNVerify.McCormick.shared_input_lower",
            "NNVerify.McCormick.shared_input_upper",
            "NNVerify.McCormick.shared_input_width",
            "NNVerify.McCormick.shared_input_width_eq",
            "NNVerify.McCormick.shared_input_gap_eq",
            "NNVerify.McCormick.shared_input_normalized_le",
            "NNVerify.McCormick.attention_tightness",
            "NNVerify.McCormick.attention_gap_linear_in_eps",
        ];
        let count = c005_names
            .iter()
            .filter(|n| env.get_const(&Name::from_string(n)).is_some())
            .count();
        assert_eq!(count, 8, "Expected 8 C005 declarations, found {}", count);
    });
}
