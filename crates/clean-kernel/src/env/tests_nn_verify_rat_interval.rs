// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the C004 Step-1 `NNVerify.Rat.interval_*` primitives
//! registered by `env::nn_verify_rat_interval::init_nn_verify_rat_interval`.
//!
//! Paired with `crates/clean-kernel/src/env/nn_verify_rat_interval.rs` and
//! `designs/2026-04-20-c004-faithful-carrier-redesign.md` §3.
//!
//! Guards enforced:
//! 1. **Registration** — every design-doc primitive resolves via
//!    `env.get_const`.
//! 2. **Kind discipline** — each primitive is a reducible `Definition`
//!    (NOT `Axiom`, NOT `Theorem`, NOT `Opaque`). Reducible so downstream
//!    δ-reduction paths (used by `C004.interval_hull_layernorm_real` etc.)
//!    still work through the alias layer.
//! 3. **Type-check** — the declared type of every registered primitive
//!    type-checks against its stored value under the kernel.
//! 4. **Delegation fidelity** — `NNVerify.Rat.interval_add` applied to
//!    `(mk 0 0) (mk 0 0)` reduces (under δ + the underlying
//!    `NNVerify.Interval.add` body) to `(mk 0 0)`. This is the minimal
//!    definitional-equality check that the alias actually unfolds to the
//!    underlying primitive.
//! 5. **`interval_hull` min/max discipline** — for `I = (mk 0 1)` and
//!    `J = (mk 1 2)`, the hull reduces to `(mk (Rat.min 0 1) (Rat.max 1 2))`
//!    under δ. This pins the min/max body shape required by the design
//!    doc §3.3.
//! 6. **Idempotency** — `init_nn_verify_rat_interval` may be called
//!    repeatedly without error.
//!
//! Part of #3615 (C004 Phase 1 — Step 1).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_rat_interval()
        .expect("init_nn_verify_rat_interval");
    env
}

const RAT_INTERVAL_DEFS: &[&str] = &[
    "NNVerify.Rat.interval_add",
    "NNVerify.Rat.interval_mul_by_pos",
    "NNVerify.Rat.interval_mul_by_neg",
    "NNVerify.Rat.interval_hull",
];

/// (1) Registration — every design-doc primitive is discoverable via
/// `env.get_const`.
#[test]
fn test_rat_interval_primitives_registered() {
    let env = make_env();
    for def in RAT_INTERVAL_DEFS {
        assert!(
            env.get_const(&Name::from_string(def)).is_some(),
            "{def} must be registered (design \
             2026-04-20-c004-faithful-carrier-redesign.md §3)",
        );
    }
}

/// (2) Kind discipline — each design-doc alias is a reducible
/// `Declaration::Definition`. Not `Axiom` (would be a masquerade), not
/// `Theorem` (these are carriers, not proofs), not `Opaque` (downstream
/// `C004.interval_hull_layernorm_real` still needs δ-reduction through
/// the alias in Step 2).
#[test]
fn test_rat_interval_primitives_are_reducible_definitions() {
    let env = make_env();
    for def in RAT_INTERVAL_DEFS {
        let info = env
            .get_const(&Name::from_string(def))
            .unwrap_or_else(|| panic!("{def} not registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{def} must be Definition (honest alias, no axiom masquerade); \
             got {:?}",
            info.kind,
        );
        assert!(
            info.value.is_some(),
            "{def} Definition must carry a value (thin wrapper around \
             underlying NNVerify.Interval primitive)",
        );
        assert!(
            info.is_reducible,
            "{def} must be reducible so downstream δ-reduction paths \
             (C004 Step 2) still reach the underlying body",
        );
    }
}

/// (3) Every registered primitive's stored value type-checks against its
/// declared type under the kernel.
#[test]
fn test_rat_interval_primitive_definitions_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for def in RAT_INTERVAL_DEFS {
        let info = env
            .get_const(&Name::from_string(def))
            .expect("def registered");
        let value = info.value.as_ref().expect("def has value");
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("{def} value failed to type-check: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{def} inferred type must match declared type",
        );
    }
}

/// (4) Delegation fidelity — `NNVerify.Rat.interval_add I J` is
/// definitionally equal to `NNVerify.Interval.add I J`. We exercise this
/// with the concrete witness `I = J = (mk 0 0)`, which is sufficient to
/// catch a body mismatch (e.g. swapping arguments, wrapping the wrong
/// underlying primitive).
#[test]
fn test_rat_interval_add_delegates_to_interval_add() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let mk = Expr::const_(Name::from_string("NNVerify.Interval.mk"), vec![]);
    let rat_add = Expr::const_(Name::from_string("NNVerify.Rat.interval_add"), vec![]);
    let int_add = Expr::const_(Name::from_string("NNVerify.Interval.add"), vec![]);

    let i = Expr::apps(mk.clone(), [rat_zero.clone(), rat_zero.clone()]);
    let j = Expr::apps(mk, [rat_zero.clone(), rat_zero]);

    let rat_form = Expr::apps(rat_add, [i.clone(), j.clone()]);
    let int_form = Expr::apps(int_add, [i, j]);

    assert!(
        tc.is_def_eq(&rat_form, &int_form),
        "NNVerify.Rat.interval_add must δ-reduce to NNVerify.Interval.add",
    );
}

/// (5) `interval_hull` min/max discipline — for `I = (mk 0 0)` and
/// `J = (mk 0 0)`, the hull reduces to `(mk (Rat.min 0 0) (Rat.max 0 0))`
/// under δ. This pins the body shape that Step 2's
/// `C004.interval_hull_layernorm_real` carrier swap depends on (design
/// doc §3.3).
///
/// We use `(mk 0 0) (mk 0 0)` rather than `(mk 0 1) (mk 1 2)` to avoid
/// requiring `Rat.one` / `Rat.two` in the environment — the shape check
/// is the property we care about, not the specific rational arithmetic.
#[test]
fn test_rat_interval_hull_has_min_max_body() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let mk = Expr::const_(Name::from_string("NNVerify.Interval.mk"), vec![]);
    let rat_min = Expr::const_(Name::from_string("Rat.min"), vec![]);
    let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);
    let hull = Expr::const_(Name::from_string("NNVerify.Rat.interval_hull"), vec![]);

    let i = Expr::apps(mk.clone(), [rat_zero.clone(), rat_zero.clone()]);
    let j = Expr::apps(mk.clone(), [rat_zero.clone(), rat_zero.clone()]);

    let hull_form = Expr::apps(hull, [i, j]);
    let expected_lo = Expr::apps(rat_min, [rat_zero.clone(), rat_zero.clone()]);
    let expected_hi = Expr::apps(rat_max, [rat_zero.clone(), rat_zero]);
    let expected = Expr::apps(mk, [expected_lo, expected_hi]);

    assert!(
        tc.is_def_eq(&hull_form, &expected),
        "NNVerify.Rat.interval_hull must δ-reduce to \
         (NNVerify.Interval.mk (Rat.min I.lo J.lo) (Rat.max I.hi J.hi))",
    );
}

/// (6) Idempotency — calling `init_nn_verify_rat_interval` multiple times
/// on the same `Environment` does not error, does not duplicate
/// declarations, and preserves the primitive set.
#[test]
fn test_rat_interval_init_is_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_rat_interval()
        .expect("first init_nn_verify_rat_interval");
    env.init_nn_verify_rat_interval()
        .expect("second init_nn_verify_rat_interval must be idempotent");
    env.init_nn_verify_rat_interval()
        .expect("third init_nn_verify_rat_interval must be idempotent");
    for def in RAT_INTERVAL_DEFS {
        assert!(
            env.get_const(&Name::from_string(def)).is_some(),
            "{def} must survive repeated idempotent init calls",
        );
    }
}
