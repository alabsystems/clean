// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wave-8 R10 MASQUERADE audit guard tests (#3593) for
//! `NNVerify.C010.both_compute_exact_affine` and its supporting
//! `NNVerify.C010.affine_combined` alias carrier.
//!
//! Context: prior to the 2026-04-20 demasquerade commit,
//! `both_compute_exact_affine` was a `Declaration::Theorem` whose proof
//! term was
//! `fun k od W b inp => @rfl (IB (od k)) (linear_propagate_network k od W b inp)`.
//! That `Eq.refl` proof type-checked ONLY because `affine_combined` was
//! a reducible `Declaration::Definition` whose body was literally
//! `NNVerify.Zonotope.linear_propagate_network`, so both sides of
//! `zonotope_linear_propagate_network = affine_combined` delta-unfolded
//! to the same term. Per
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M4,
//! this is a MASQUERADE (alias-collapse via reducible Definition +
//! Eq.refl root). See
//! `reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md`
//! Finding 2.
//!
//! Branch A action taken:
//! - `NNVerify.C010.both_compute_exact_affine` -> `Declaration::Axiom`
//!   on the original Pi type. No stored proof value.
//! - `NNVerify.C010.affine_combined` -> `Declaration::Opaque` (same
//!   body; only the declaration kind flipped). Opaques do not
//!   delta-unfold during `def_eq`, so no future downstream theorem can
//!   silently rebuild the same MASQUERADE.
//!
//! 2026-04-27 follow-up: `both_compute_exact_affine` is retired as a global
//! axiom by strengthening its type with an explicit local equality premise
//! and registering a theorem that returns that premise. These tests now pin
//! both the local-evidence theorem and the opaque alias-carrier invariant.

use crate::env::{ConstantKind, Environment};
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_zonotope_crown()
        .expect("init_nn_verify_zonotope_crown");
    env
}

/// `both_compute_exact_affine` is a hypothesis-wrapped theorem. Its proof
/// returns explicit local equality evidence and must not depend on a global
/// C010 axiom or unfold `affine_combined`.
#[test]
fn test_both_compute_exact_affine_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.C010.both_compute_exact_affine",
        ))
        .expect("NNVerify.C010.both_compute_exact_affine should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "both_compute_exact_affine should be a hypothesis-wrapped Theorem; got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "both_compute_exact_affine theorem must carry its local-evidence proof",
    );
    let deps = env
        .axiom_deps(&Name::from_string(
            "NNVerify.C010.both_compute_exact_affine",
        ))
        .expect("both_compute_exact_affine should be registered");
    assert!(
        deps.is_empty(),
        "hypothesis-wrapped both_compute_exact_affine must not depend on \
         global axioms; got {:?}",
        deps,
    );
}

/// `NNVerify.C010.affine_combined` must be Opaque (not a reducible
/// Definition). A reducible Definition whose body is
/// `NNVerify.Zonotope.linear_propagate_network` is precisely the alias
/// carrier that lets Eq.refl-based MASQUERADE proofs of
/// `both_compute_exact_affine` type-check.
#[test]
fn test_affine_combined_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C010.affine_combined"))
        .expect("NNVerify.C010.affine_combined should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "affine_combined must be Opaque after the #3593 wave-8 \
         demasquerade; reducible Definition re-opens the MASQUERADE \
         loophole (delta-reduction to linear_propagate_network)",
    );
    assert!(
        !info.is_reducible,
        "affine_combined must not be reducible; got is_reducible=true",
    );
    assert!(
        info.value.is_some(),
        "Opaque must retain its body (reference to \
         NNVerify.Zonotope.linear_propagate_network)",
    );
}

/// Regression: the hypothesis-wrapped statement of `both_compute_exact_affine`
/// must still type-check at the kernel level.
#[test]
fn test_both_compute_exact_affine_theorem_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C010.both_compute_exact_affine"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("both_compute_exact_affine theorem type should still infer");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}
