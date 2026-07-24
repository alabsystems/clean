// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral tests for issue #3432: multi-ctor enum `deriving DecidableEq`
//! must produce a *reducing* `Decidable` instance, not a `sorry`-inhabited
//! stub. `decide (x = y)` must compute to `Bool.true` / `Bool.false` through
//! iota reduction on `casesOn` + the `decide` native reducer.
//!
//! Follow-up to #3431 which left the multi-ctor body as `sorry`.

use super::*;

use clean_kernel::TypeChecker;

/// Helper: set up a fresh env with prelude, elaborate the given inductive
/// `deriving DecidableEq`, and register both the inductive and the
/// derived instance into the environment.
fn setup_env_with_derived_deq(decl_src: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(decl_src).expect("parse");
    crate::elaborate_decl_and_register(&mut env, &decl).expect("register inductive + deriving");
    env
}

/// Assert that `head` unfolds (under WHNF) to a constant with the given name.
/// Returns the post-WHNF expression so tests can inspect arguments.
fn assert_whnf_head(tc: &TypeChecker<'_>, e: &Expr, expected: &str, context: &str) -> Expr {
    let w = tc.whnf(e);
    let head = w.get_app_fn();
    let name = match head.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => panic!(
            "{context}: expected WHNF head Const({expected}), got {:?}\n  full whnf: {:?}",
            other, w
        ),
    };
    assert_eq!(
        name, expected,
        "{context}: expected WHNF head const {expected}, got {name}\n  full whnf: {w:?}"
    );
    w
}

/// Core #3432 test: `decide (Color.red = Color.red)` must reduce to `Bool.true`.
#[test]
fn test_issue3432_decide_reduces_is_true_for_same_ctor() {
    let env = setup_env_with_derived_deq(
        r"inductive Color
| red
| green
| blue
deriving DecidableEq",
    );

    // Build: @instColorDecidableEq Color.red Color.red : Decidable (Color.red = Color.red)
    // Note: the instance value is the body without the instance-wrapper lambdas
    //       (monomorphic => no universe params).
    let inst = Expr::const_(Name::from_string("instColorDecidableEq"), vec![]);
    let red = Expr::const_(Name::from_string("Color.red"), vec![]);
    let applied = Expr::app(Expr::app(inst.clone(), red.clone()), red.clone());

    let tc = TypeChecker::new(&env);

    // After WHNF the instance application MUST land at `Decidable.isTrue _`
    // (it must not stay as `sorry` or `sorryAx`).
    let whnf_inst = assert_whnf_head(
        &tc,
        &applied,
        "Decidable.isTrue",
        "inst Color.red Color.red",
    );

    // Make sure sorry is nowhere in the WHNF'd tree.
    let serialized = format!("{whnf_inst:?}");
    assert!(
        !serialized.contains("sorry") && !serialized.contains("sorryAx"),
        "decide body for same-ctor must not contain sorry:\n{serialized}"
    );
}

/// `decide (Color.red = Color.green)` must reduce to `Bool.false`.
#[test]
fn test_issue3432_decide_reduces_is_false_for_distinct_ctors() {
    let env = setup_env_with_derived_deq(
        r"inductive Color
| red
| green
| blue
deriving DecidableEq",
    );

    let inst = Expr::const_(Name::from_string("instColorDecidableEq"), vec![]);
    let red = Expr::const_(Name::from_string("Color.red"), vec![]);
    let green = Expr::const_(Name::from_string("Color.green"), vec![]);
    let applied = Expr::app(Expr::app(inst.clone(), red), green);

    let tc = TypeChecker::new(&env);
    let _ = assert_whnf_head(
        &tc,
        &applied,
        "Decidable.isFalse",
        "inst Color.red Color.green",
    );
}

/// End-to-end behavioral test (the load-bearing #3432 acceptance criterion):
/// `decide (Color.red = Color.red)` WHNFs directly to `Bool.true` without
/// any manual pre-reduction of the instance. Confirms the kernel's
/// `reduce_native` special-case for `decide` (pre-WHNFs the instance arg)
/// connects with the generated `instColorDecidableEq` body.
#[test]
fn test_issue3432_decide_color_red_red_whnfs_to_bool_true() {
    let env = setup_env_with_derived_deq(
        r"inductive Color
| red
| green
| blue
deriving DecidableEq",
    );

    let color = Expr::const_(Name::from_string("Color"), vec![]);
    let red = Expr::const_(Name::from_string("Color.red"), vec![]);
    let eq_prop = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                color,
            ),
            red.clone(),
        ),
        red.clone(),
    );

    let inst_const = Expr::const_(Name::from_string("instColorDecidableEq"), vec![]);
    let inst = Expr::app(Expr::app(inst_const, red.clone()), red);

    let decide_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("decide"), vec![]), eq_prop),
        inst,
    );

    let tc = TypeChecker::new(&env);
    let w = tc.whnf(&decide_expr);
    match w.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "Bool.true",
                "decide (Color.red = Color.red) must reduce to Bool.true, \
                 got {name:?}"
            );
        }
        other => panic!(
            "decide (Color.red = Color.red) must reduce to a Bool constant, \
             got {:?}\n  full whnf: {:?}",
            other, w
        ),
    }
}

/// End-to-end: `decide (Color.red = Color.green)` WHNFs to `Bool.false`.
#[test]
fn test_issue3432_decide_color_red_green_whnfs_to_bool_false() {
    let env = setup_env_with_derived_deq(
        r"inductive Color
| red
| green
| blue
deriving DecidableEq",
    );

    let color = Expr::const_(Name::from_string("Color"), vec![]);
    let red = Expr::const_(Name::from_string("Color.red"), vec![]);
    let green = Expr::const_(Name::from_string("Color.green"), vec![]);
    let eq_prop = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                color,
            ),
            red.clone(),
        ),
        green.clone(),
    );

    let inst_const = Expr::const_(Name::from_string("instColorDecidableEq"), vec![]);
    let inst = Expr::app(Expr::app(inst_const, red), green);

    let decide_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("decide"), vec![]), eq_prop),
        inst,
    );

    let tc = TypeChecker::new(&env);
    let w = tc.whnf(&decide_expr);
    match w.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "Bool.false",
                "decide (Color.red = Color.green) must reduce to Bool.false, \
                 got {name:?}"
            );
        }
        other => panic!(
            "decide (Color.red = Color.green) must reduce to a Bool constant, \
             got {:?}",
            other
        ),
    }
}

/// Sanity: 2-ctor enum reduces correctly via the same code path.
/// Uses the direct instance-WHNF check (reduces to `Decidable.isTrue _`
/// / `isFalse _`) since that is the load-bearing property.
#[test]
fn test_issue3432_two_ctor_enum_instance_reduces() {
    let env = setup_env_with_derived_deq(
        r"inductive Bit
| zero
| one
deriving DecidableEq",
    );

    let b_zero = Expr::const_(Name::from_string("Bit.zero"), vec![]);
    let b_one = Expr::const_(Name::from_string("Bit.one"), vec![]);

    let mk_inst = |a: &Expr, b: &Expr| -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("instBitDecidableEq"), vec![]),
                a.clone(),
            ),
            b.clone(),
        )
    };

    let tc = TypeChecker::new(&env);

    // Decidable.isTrue for same ctor
    let _ = assert_whnf_head(
        &tc,
        &mk_inst(&b_zero, &b_zero),
        "Decidable.isTrue",
        "Bit.zero = Bit.zero",
    );
    let _ = assert_whnf_head(
        &tc,
        &mk_inst(&b_one, &b_one),
        "Decidable.isTrue",
        "Bit.one = Bit.one",
    );

    // Decidable.isFalse for distinct ctors
    let _ = assert_whnf_head(
        &tc,
        &mk_inst(&b_zero, &b_one),
        "Decidable.isFalse",
        "Bit.zero = Bit.one",
    );
    let _ = assert_whnf_head(
        &tc,
        &mk_inst(&b_one, &b_zero),
        "Decidable.isFalse",
        "Bit.one = Bit.zero",
    );
}

/// Regression guard: the generated `instColorDecidableEq` constant must not
/// transitively reference `sorryAx` / `sorry`. (Pure structural check —
/// complements the behavioral reduce-to-Bool tests above.)
#[test]
fn test_issue3432_generated_term_is_sorry_free() {
    let env = setup_env_with_derived_deq(
        r"inductive Color
| red
| green
| blue
deriving DecidableEq",
    );

    let inst_name = Name::from_string("instColorDecidableEq");
    let decl = env
        .get_const(&inst_name)
        .unwrap_or_else(|| panic!("instColorDecidableEq should be in env"));

    // Serialize the value and the type; neither should mention sorry.
    let val_str = format!("{:?}", decl.value);
    let ty_str = format!("{:?}", decl.type_);
    assert!(
        !val_str.contains("sorry") && !val_str.contains("sorryAx"),
        "instColorDecidableEq value must not reference sorry:\n{val_str}"
    );
    assert!(
        !ty_str.contains("sorry") && !ty_str.contains("sorryAx"),
        "instColorDecidableEq type must not reference sorry:\n{ty_str}"
    );

    // And the value must exist (not an axiom/opaque).
    assert!(
        decl.value.is_some(),
        "instColorDecidableEq must have a value (not a bare axiom): {decl:?}"
    );
}
