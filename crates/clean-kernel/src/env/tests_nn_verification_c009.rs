// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral tests for C009 post-IBP-wrapper axiom retirement state.
//!
//! These tests assert declaration kind and axiom-closure structure — not
//! just registration — per design doc Proof Soundness Rules ("Proof quality
//! in test assertions").
//!
//! Scope of the 2026-04-27 C009 IBP-wrapper retirement:
//!
//! The 3 IBP-wrapping claims (`ibp_wrapping_single_layer`,
//! `ibp_wrapping_compounds`, `ibp_wrapping_correlation_loss`) had been
//! retyped under #3462 from sorry-inhabited Opaques (`type: Sort(succ(u))`,
//! value `@sorry.{succ(succ(u))} Sort(succ(u))`) into `Declaration::Theorem`
//! entries with type `True:Prop` and value `True.intro`. The 2026-04-19
//! vacuity audit flagged that retype as Rule M3 statement-rewriting — a
//! MASQUERADE — because the original IBP width-bound content was not
//! encoded in the `True` type.
//!
//! The 2026-04-27 retirement keeps those three out of the global axiom set by
//! registering each as a hypothesis-wrapped `Declaration::Theorem`. Each
//! theorem type is a concrete C009 width equality obligation implying itself,
//! and the proof term is the local premise. Tests assert:
//!
//!   1. Each declaration is `ConstantKind::Theorem` with a stored proof value.
//!   2. The stored value is a local-evidence lambda, not `True.intro`,
//!      `Eq.refl`, or a global C009 axiom reference.
//!   3. The declared `type_` is a Pi/arrow over an explicit equality
//!      obligation — NOT the bare `Const("True")` that #3462 introduced.
//!   4. The transitive axiom closure contains no `sorry` / `sorryAx` /
//!      `True.intro` references and no C009 IBP wrapper axiom names.
//!   5. The 10 non-IBP-wrapping former-axioms remain sorry-inhabited
//!      Opaques (regression fence for out-of-scope groups).
//!   6. Counting invariant: 3 Theorems + 17 Opaques + 0 Axioms in the
//!      `NNVerification.` namespace (3 data Definitions are excluded by
//!      `ConstantKind` filter).

use super::*;
use crate::env::ConstantKind;
use crate::expr::ExprKind;
use crate::name::Name;

/// The three IBP-wrapping claims retired as local-evidence theorems.
const C009_IBP_WRAPPING_THEOREMS: &[&str] = &[
    "NNVerification.ibp_wrapping_single_layer",
    "NNVerification.ibp_wrapping_compounds",
    "NNVerification.ibp_wrapping_correlation_loss",
];

/// The 10 former-axioms that remain sorry-inhabited Opaques after #3580.
/// These are the regression fence: the Branch A demotion must not leak
/// into groups that were not in scope.
const C009_REMAINING_SORRY_OPAQUES: &[&str] = &[
    // Crown correlation (3)
    "NNVerification.crown_backsubstitution",
    "NNVerification.crown_combined_matrix",
    "NNVerification.crown_correlation_retained",
    // Exponential gap (4)
    "NNVerification.norm_product_vs_product_norm",
    "NNVerification.crown_uses_product",
    "NNVerification.ibp_uses_product_of_norms",
    "NNVerification.crown_ibp_ratio_exponential",
    // Depth scaling (2)
    "NNVerification.ratio_monotone_depth",
    "NNVerification.ratio_limit_zero",
    // Summary conjecture (1)
    "NNVerification.c009_exponentially_tighter_than_ibp",
];

/// Helper: fresh env initialized through the full C009 init path.
///
/// Exercises the kernel `add_decl` TC path for every declaration — so
/// "registered" means "type-checked by the kernel", not "blindly inserted".
fn c009_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verification_c009()
        .expect("init_nn_verification_c009 should succeed");
    env
}

/// Each IBP-wrapping declaration must be a `ConstantKind::Theorem`
/// with a local-evidence proof value.
#[test]
fn test_c009_ibp_wrapping_is_hypothesis_wrapped_theorem() {
    let env = c009_env();
    for name in C009_IBP_WRAPPING_THEOREMS {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("missing declaration: {name}"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be ConstantKind::Theorem after C009 IBP-wrapper \
             axiom retirement. Got: {:?}",
            info.kind,
        );
        assert!(
            info.value.is_some(),
            "{name} hypothesis-wrapped Theorem must carry a local-evidence \
             proof value.",
        );
    }
}

/// Each IBP-wrapping declaration's type must be an explicit premise arrow
/// over a C009 width-equality obligation — NOT the bare `Const("True")`
/// that #3462 introduced.
///
/// Walking the expression tree is the behavioral part: a future regression
/// that re-routed the type back to `True:Prop` would fail this test.
#[test]
fn test_c009_ibp_wrapping_type_is_not_true_prop() {
    let env = c009_env();
    let true_name = Name::from_string("True");
    for name in C009_IBP_WRAPPING_THEOREMS {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        match info.type_.kind() {
            ExprKind::Pi(_, domain, codomain) => {
                let domain_dbg = format!("{:?}", domain);
                let codomain_dbg = format!("{:?}", codomain);
                assert!(
                    domain_dbg.contains("Eq")
                        && domain_dbg.contains("NNVerification")
                        && domain_dbg.contains("c009_ibp_width")
                        && domain_dbg.contains("c009_input_radius"),
                    "{name} premise must expose the C009 IBP width equality; got {domain_dbg}",
                );
                assert_eq!(
                    domain_dbg, codomain_dbg,
                    "{name} must have local-evidence shape P -> P",
                );
            }
            ExprKind::Const(n, _) => {
                panic!(
                    "{name} type must be a local-evidence Pi after C009 \
                     axiom retirement; found `Const({n})` — a regression to \
                     the #3462 True:Prop MASQUERADE carrier is likely.",
                );
            }
            ExprKind::Sort(_) => {
                panic!(
                    "{name} type must be a local-evidence Pi after C009 \
                     axiom retirement; found a Sort carrier, which would \
                     not expose the local C009 width obligation.",
                );
            }
            other => panic!(
                "{name} type must be a local-evidence Pi after C009 \
                 axiom retirement; got {other:?}",
            ),
        }
        let dbg = format!("{:?}", info.type_);
        assert!(
            !dbg.contains(&true_name.to_string()),
            "{name} type must not reference `True` after C009 axiom retirement; \
             got: {dbg}",
        );
    }
}

/// Soundness-relevant fence: the transitive axiom closure of each retired
/// C009 IBP-wrapping declaration contains NO `sorry` / `sorryAx` /
/// `True.intro` markers or global C009 IBP wrapper axiom names.
#[test]
fn test_c009_ibp_wrapping_no_sorry_true_intro_or_global_axiom_in_closure() {
    let env = c009_env();
    for name in C009_IBP_WRAPPING_THEOREMS {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("axiom_deps({name}) returned None"));
        let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        for n in &dep_names {
            assert!(
                !n.contains("sorry") && !n.contains("sorryAx"),
                "{name} transitive axiom closure must not contain a sorry \
                 reference after C009 axiom retirement; found: {n}. Full deps: \
                 {:?}",
                dep_names,
            );
            assert!(
                n != "True.intro",
                "{name} transitive axiom closure must not contain \
                 `True.intro` after C009 axiom retirement (the \
                 #3462 MASQUERADE carrier). Full deps: {:?}",
                dep_names,
            );
        }
        assert!(
            !dep_names
                .iter()
                .any(|n| C009_IBP_WRAPPING_THEOREMS.contains(&n.as_str())),
            "{name} closure must not reference a global C009 IBP wrapper \
             axiom/theorem. Full deps: {:?}",
            dep_names,
        );
    }
}

#[test]
fn test_c009_ibp_wrapping_proof_is_local_lambda() {
    let env = c009_env();
    for name in C009_IBP_WRAPPING_THEOREMS {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} theorem value missing"));
        match value.kind() {
            ExprKind::Lam(_, _, body) => {
                assert!(
                    matches!(body.kind(), ExprKind::BVar(0)),
                    "{name} proof must return the local hypothesis directly; got {body:?}",
                );
            }
            other => panic!("{name} proof must be a lambda over local evidence; got {other:?}"),
        }
        let dbg = format!("{:?}", value);
        assert!(
            !dbg.contains("True.intro")
                && !dbg.contains("Eq.refl")
                && !dbg.contains("sorry")
                && !dbg.contains("sorryAx"),
            "{name} proof must not use True.intro, Eq.refl, or sorry; got {dbg}",
        );
    }
}

/// Regression fence: the 10 former-axioms outside the IBP-wrapper scope must
/// stay as Opaques. If a subsequent change accidentally converts them via
/// a broader demasquerade sweep, this test fails — forcing an explicit
/// review of soundness implications per group.
#[test]
fn test_c009_non_ibp_wrapping_still_opaque() {
    let env = c009_env();
    for name in C009_REMAINING_SORRY_OPAQUES {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("missing declaration: {name}"));
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} must still be Opaque pending per-group remediation; \
             was {:?}",
            info.kind,
        );
    }
}

/// Top-line counting invariant: after C009 IBP-wrapper retirement, C009 registers
///   3 Definition + 7 data Opaque + 3 IBP-wrapping Theorem
///   + 10 sorry-inhabited Opaque = 23 declarations.
///
/// Keeps Branch A in lockstep with the #3376 Phase 2 inventory total so
/// follow-up Branch B work can migrate one at a time without drifting
/// the count.
#[test]
fn test_c009_inventory_after_ibp_wrapper_retirement() {
    let env = c009_env();
    let mut theorem_count = 0usize;
    let mut opaque_count = 0usize;
    let mut axiom_count = 0usize;
    // Walk only C009-namespaced constants. C009 is the only conjecture
    // using `NNVerification.` (others use `NNVerify.`), so the prefix
    // match is tight.
    for info in env.constants() {
        let s = info.name.to_string();
        if !s.starts_with("NNVerification.") {
            continue;
        }
        match info.kind {
            ConstantKind::Theorem => theorem_count += 1,
            ConstantKind::Opaque => opaque_count += 1,
            ConstantKind::Axiom => axiom_count += 1,
            _ => {}
        }
    }
    assert_eq!(
        theorem_count, 3,
        "C009 IBP-wrapper retirement registers exactly 3 Theorems; \
         Got {theorem_count}",
    );
    assert_eq!(
        axiom_count, 0,
        "C009 IBP-wrapper retirement leaves no NNVerification. Axioms; \
         got {axiom_count}",
    );
    // 7 data Opaques + 10 remaining sorry-inhabited Opaques = 17.
    assert_eq!(
        opaque_count, 17,
        "C009 IBP-wrapper retirement leaves 17 C009 Opaques (7 data + 10 sorry); \
         got {opaque_count}",
    );
}
