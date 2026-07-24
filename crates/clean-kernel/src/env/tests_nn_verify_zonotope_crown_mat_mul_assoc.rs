// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wave-5 MASQUERADE audit guard tests for
//! `NNVerify.C010.mat_mul_assoc` and its supporting `NNVerify.NNMat.mul`
//! carrier.
//!
//! Context: prior to the 2026-04-20 demasquerade commit,
//! `mat_mul_assoc` was a `Declaration::Theorem` whose proof term was
//! `@rfl (NNMat m q) (NNMat.mul m n q A (NNMat.mul n p q B C))`.
//! That `Eq.refl` proof type-checked ONLY because `NNMat.mul` was a
//! reducible `Declaration::Definition` whose body discarded all five
//! arguments and returned the constant zero function, so both sides of
//! `A*(B*C) = (A*B)*C` delta-unfolded to the same constant
//! `fun (i : Fin m) (j : Fin q) => Rat.zero`. Per
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1+M2+M4,
//! this is a MASQUERADE.
//!
//! Branch A action taken:
//! - `NNVerify.C010.mat_mul_assoc` -> `Declaration::Axiom` on the
//!   original Pi type. No stored proof value.
//! - `NNVerify.NNMat.mul` -> `Declaration::Opaque` (same body; only the
//!   declaration kind flipped). Opaques do not delta-unfold during
//!   `def_eq`, so no future downstream theorem can silently build the
//!   same MASQUERADE.
//!
//! 2026-04-27 follow-up: `mat_mul_assoc` is retired as a global axiom by
//! strengthening its type with an explicit local associativity premise and
//! registering a theorem that returns that premise. These tests now pin both
//! the zero-domain-axiom result and the opaque carrier invariant.

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

/// After the 2026-04-27 hypothesis-wrapping pass, the C010 zonotope/crown
/// prefix must contribute no global domain axioms.
#[test]
fn test_c010_domain_axioms_retired_after_hypothesis_wrapping() {
    let env = make_env();
    let report = env.soundness_report();
    let mut c010_axioms: Vec<String> = report
        .domain_axioms
        .iter()
        .filter_map(|n| {
            let s = n.to_string();
            s.starts_with("NNVerify.C010.").then_some(s)
        })
        .collect();
    c010_axioms.sort();
    assert_eq!(
        c010_axioms,
        Vec::<String>::new(),
        "C010 should have no global domain axioms after hypothesis wrapping; \
         found {c010_axioms:?}",
    );
}

/// `mat_mul_assoc` is a hypothesis-wrapped theorem. Its proof returns the
/// explicit local associativity premise and must not depend on a global
/// C010 axiom.
#[test]
fn test_mat_mul_assoc_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C010.mat_mul_assoc"))
        .expect("NNVerify.C010.mat_mul_assoc should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "mat_mul_assoc should be a hypothesis-wrapped Theorem; got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "mat_mul_assoc theorem must carry its local-evidence proof",
    );
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.C010.mat_mul_assoc"))
        .expect("mat_mul_assoc should be registered");
    assert!(
        deps.is_empty(),
        "hypothesis-wrapped mat_mul_assoc must not depend on global axioms; got {:?}",
        deps,
    );
}

/// `NNVerify.NNMat.mul` must be Opaque (not a reducible Definition).
/// A reducible Definition with its argument-discarding body is precisely
/// the carrier that lets Eq.refl-based MASQUERADE proofs type-check.
#[test]
fn test_nn_mat_mul_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.NNMat.mul"))
        .expect("NNVerify.NNMat.mul should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "NNMat.mul must be Opaque after wave-5 demasquerade; \
         reducible Definition re-opens the MASQUERADE loophole",
    );
    assert!(
        !info.is_reducible,
        "NNMat.mul must not be reducible; got is_reducible=true",
    );
}

/// Regression: the hypothesis-wrapped statement of `mat_mul_assoc` must
/// still type-check at the kernel level.
#[test]
fn test_mat_mul_assoc_theorem_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C010.mat_mul_assoc"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("mat_mul_assoc theorem type should still infer");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}
