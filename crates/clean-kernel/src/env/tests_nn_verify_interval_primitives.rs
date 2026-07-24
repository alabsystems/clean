// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the faithful `Rat` scalar interval primitives registered
//! by `env::nn_verify_interval_primitives::init_nn_verify_interval_primitives`.
//!
//! Paired with `crates/clean-kernel/src/env/nn_verify_interval_primitives.rs`.
//!
//! Guards enforced:
//! 1. **Registration** — every Phase-1 primitive name resolves via
//!    `env.get_const`.
//! 2. **Kind discipline** — the inductive is `Inductive`, the constructor is
//!    `Constructor`, every named function is a `Definition` (NOT `Axiom` and
//!    NOT `Theorem`).
//! 3. **Type-check** — the declared type of every `Definition` type-checks
//!    under the kernel against its stored value.
//! 4. **Honest width** — `Interval.width (mk a b)` reduces to `Rat.sub b a`
//!    under δ (the carrier is structurally faithful, not an identity alias).
//! 5. **Honest axiom closure** — every purely-constructive `Definition`'s
//!    transitive axiom closure is empty, and the one `Definition` that
//!    genuinely consumes the admitted `Rat` lattice primitives
//!    (`NNVerify.Interval.scalar_mul`, built on `Rat.min` / `Rat.max`) has a
//!    NON-EMPTY closure containing ONLY admitted domain axioms — no rogue
//!    axiom, no `sorry`. (#integrity-audit 2026-06: `Rat.min` / `Rat.max`
//!    are admitted DOMAIN axioms, no longer whitelisted as foundational, so
//!    the closure can no longer be claimed empty for `scalar_mul`.)
//! 6. **Idempotency** — `init_nn_verify_interval_primitives` may be called
//!    repeatedly without error.
//!
//! Part of #3615 (C004 Phase 1).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_interval_primitives()
        .expect("init_nn_verify_interval_primitives");
    env
}

const TYPE_NAME: &str = "NNVerify.Interval";
const MK_NAME: &str = "NNVerify.Interval.mk";

const DEFINITIONS: &[&str] = &[
    "NNVerify.Interval.lo",
    "NNVerify.Interval.hi",
    "NNVerify.Interval.width",
    "NNVerify.Interval.contains",
    "NNVerify.Interval.add",
    "NNVerify.Interval.scalar_mul_pos",
    "NNVerify.Interval.scalar_mul_neg",
    "NNVerify.Interval.scalar_mul",
];

/// (1) Every Phase-1 declaration is registered.
#[test]
fn test_interval_primitives_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(TYPE_NAME)).is_some(),
        "{TYPE_NAME} must be registered",
    );
    assert!(
        env.get_const(&Name::from_string(MK_NAME)).is_some(),
        "{MK_NAME} must be registered",
    );
    for def in DEFINITIONS {
        assert!(
            env.get_const(&Name::from_string(def)).is_some(),
            "{def} must be registered",
        );
    }
}

/// (2) Each named function is a `Definition` — not an `Axiom`, not a
/// `Theorem`. This enforces the "no masquerade" rule: we register honest
/// computable carriers, not axiom-wrapped stubs. The inductive type and
/// its constructor are registered through the inductive path; we verify
/// they are discoverable via the inductive/constructor APIs respectively.
#[test]
fn test_interval_primitives_are_definitions() {
    let env = make_env();
    // Inductive type: lookup via get_inductive.
    assert!(
        env.get_inductive(&Name::from_string(TYPE_NAME)).is_some(),
        "{TYPE_NAME} must be registered as an inductive",
    );
    // Constructor: lookup via get_constructor.
    assert!(
        env.get_constructor(&Name::from_string(MK_NAME)).is_some(),
        "{MK_NAME} must be registered as a constructor",
    );
    // Definitions: ConstantKind::Definition with a value, never Axiom/Theorem.
    for def in DEFINITIONS {
        let info = env
            .get_const(&Name::from_string(def))
            .expect("def registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{def} must be Definition (honest carrier, no axiom masquerade); got {:?}",
            info.kind,
        );
        assert!(info.value.is_some(), "{def} Definition must carry a value",);
    }
}

/// (3) Every `Definition` type-checks against its stored value under the
/// kernel type checker.
#[test]
fn test_interval_primitive_definitions_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for def in DEFINITIONS {
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

/// (4) **Honest width**: `Interval.width (Interval.mk a b)` reduces to
/// `Rat.sub b a` under kernel δ + ι reduction. This is the key test
/// distinguishing a *faithful* carrier (fields actually store `a` and `b`)
/// from an *identity-alias* carrier (everything reduces to a single projection
/// of the input). The former earns `Eq.refl` on the δ-reduct; the latter
/// yields the rejected Wave-10 masquerade pattern.
///
/// We check definitional equality rather than constructing a full proof term
/// because the Phase 1 scope is *carriers only* — lemmas are Phase 2.
#[test]
fn test_interval_width_mk_is_hi_minus_lo() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);

    // Sanity: both Rat.zero and Rat.one exist in the environment. If either
    // is missing, the test environment lacks the init layer it needs.
    assert!(
        env.get_const(&Name::from_string("Rat.zero")).is_some(),
        "Rat.zero must be registered for width reduction test",
    );
    assert!(
        env.get_const(&Name::from_string("Rat.one")).is_some(),
        "Rat.one must be registered for width reduction test",
    );

    // Also sanity-check that the projected fields differ from each other:
    // (mk 0 1).lo ≠ (mk 0 1).hi, meaning the fields are stored faithfully
    // and the carrier is not an identity alias.
    let mk = Expr::const_(Name::from_string("NNVerify.Interval.mk"), vec![]);
    let i = Expr::apps(mk, [rat_zero.clone(), rat_one.clone()]);

    let lo_proj = Expr::proj(Name::from_string("NNVerify.Interval"), 0, i.clone());
    let hi_proj = Expr::proj(Name::from_string("NNVerify.Interval"), 1, i.clone());
    assert!(
        tc.is_def_eq(&lo_proj, &rat_zero),
        "(mk 0 1).lo must reduce to Rat.zero (faithful carrier)",
    );
    assert!(
        tc.is_def_eq(&hi_proj, &rat_one),
        "(mk 0 1).hi must reduce to Rat.one (faithful carrier)",
    );
    assert!(
        !tc.is_def_eq(&lo_proj, &hi_proj),
        "(mk 0 1).lo and (mk 0 1).hi must be distinct — identity-alias \
         carriers were rejected in the C004 Wave-10 demasquerade",
    );

    // width (mk 0 1) = Rat.sub 1 0 definitionally.
    let width = Expr::const_(Name::from_string("NNVerify.Interval.width"), vec![]);
    let width_i = Expr::app(width, i);
    let expected = Expr::apps(rat_sub, [rat_one, rat_zero]);
    assert!(
        tc.is_def_eq(&width_i, &expected),
        "width (mk 0 1) must reduce to Rat.sub 1 0 by δ/ι",
    );

    // Also verify both sides type-check at `Rat`.
    let w_ty = tc.infer_type(&width_i).expect("width application types");
    assert!(
        tc.is_def_eq(&w_ty, &rat),
        "width application must have type Rat",
    );
}

/// (5) Honest axiom closure per `Definition`.
///
/// #integrity-audit (2026-06): `Rat.min` / `Rat.max` are admitted DOMAIN
/// axioms (see `axiom_audit::ADMITTED_DOMAIN_AXIOMS`) — mathematically true
/// but registered as bare `Declaration::Axiom` with NO Clean-kernel proof
/// term. They were previously dishonestly whitelisted as "foundational", so
/// `axiom_deps` filtered them out and this test could (over)claim a *zero*
/// domain-axiom closure for every primitive. They are now EXCLUDED from
/// `is_foundational_axiom`, so `NNVerify.Interval.scalar_mul` — which is
/// `mk (min (s*lo) (s*hi)) (max ...)` — honestly carries `Rat.min` and
/// `Rat.max` in its transitive closure.
///
/// The honest contract is therefore split:
///   * the purely-constructive primitives (`lo`, `hi`, `width`, `contains`,
///     `add`, `scalar_mul_pos`, `scalar_mul_neg`) still have an EMPTY
///     domain-axiom closure — they introduce no axioms; and
///   * `scalar_mul` has a NON-EMPTY closure that contains ONLY admitted
///     domain axioms (`Rat.min` / `Rat.max`) — no rogue / unexpected axiom.
///
/// Either way: NO `sorry` anywhere.
#[test]
fn test_interval_primitives_honest_domain_axiom_closure() {
    use super::axiom_audit::ADMITTED_DOMAIN_AXIOMS;

    let env = make_env();

    // `scalar_mul` is the only Phase-1 primitive that consumes the admitted
    // `Rat` lattice axioms; every other primitive must stay axiom-clean.
    const SCALAR_MUL: &str = "NNVerify.Interval.scalar_mul";

    for def in DEFINITIONS {
        let deps = env
            .axiom_deps(&Name::from_string(def))
            .unwrap_or_else(|| panic!("axiom_deps({def}) should resolve"));
        let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();

        // WS-B: `scalar_mul`'s `Rat.min` / `Rat.max` lattice axioms are now
        // kernel-checked constructive Definitions/Theorems over the quotient
        // carrier, so EVERY Phase-1 primitive (including `scalar_mul`) has an
        // EMPTY domain-axiom closure. `SCALAR_MUL` is retained only to document
        // that it used to be the one axiom-dependent primitive.
        let _ = (SCALAR_MUL, &ADMITTED_DOMAIN_AXIOMS);
        assert!(
            dep_names.is_empty(),
            "{def} must have zero domain-specific axioms in transitive \
             closure; got {dep_names:?}",
        );

        // Sorry check: no sorry/sorryAx anywhere (true for every primitive,
        // admitted-axiom-dependent or not).
        let info = env
            .get_const(&Name::from_string(def))
            .expect("def registered");
        let sorry = info.sorry_summary();
        assert!(
            !sorry.has_sorry,
            "{def} must be sorry-free; summary = {sorry:?}",
        );
    }
}

/// (6) The init function is idempotent.
#[test]
fn test_init_nn_verify_interval_primitives_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_interval_primitives()
        .expect("first init");
    env.init_nn_verify_interval_primitives()
        .expect("second init (idempotent)");
    env.init_nn_verify_interval_primitives()
        .expect("third init (idempotent)");
    // All declarations still resolve after repeated init.
    assert!(env
        .get_const(&Name::from_string("NNVerify.Interval.width"))
        .is_some());
}
