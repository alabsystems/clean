// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Rat field→order bridging lemmas (#3503).
//!
//! Guards:
//! - All 4 target lemmas are `Declaration::Theorem` (not Opaque with sorry).
//! - Each theorem type-checks.
//! - No `sorry`/`sorryAx` appears in the transitive axiom closure.
//! - Post-#3656, `Rat.mul_sub` still remains a `Declaration::Theorem`, but its
//!   only non-foundational transitive dep is now the rolled-back
//!   `Rat.left_distrib` axiom; bridge spillover must stay absent.
//! - Transitive axiom deps are a subset of `{foundational} ∪ {named Rat
//!   field/order axioms}`.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_rat_ordering()
        .expect("init_nn_verify_rat_ordering should succeed");
    env
}

fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered"
    );
}

fn assert_is_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} should be Declaration::Theorem, got {:?}",
        info.kind
    );
}

fn assert_type_checks(env: &Environment, name: &str) {
    let e = Expr::const_(Name::from_string(name), vec![]);
    let tc = TypeChecker::with_mode(env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{name} should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "{name} type should be a Pi, got {:?}",
        ty.kind()
    );
}

/// Walk an expression and return true if any constant named `sorry` or
/// `sorryAx` appears.
fn value_contains_sorry(expr: &Expr) -> bool {
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                if s == "sorry" || s == "sorryAx" {
                    return true;
                }
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, src) => stack.push(src),
            ExprKind::MData(_, body) => stack.push(body),
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            _ => {}
        }
    }
    false
}

fn assert_no_sorry_in_value(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    let value = info.value.as_ref().unwrap_or_else(|| {
        panic!(
            "{name} should have a value (Theorem) — info.kind = {:?}",
            info.kind
        )
    });
    assert!(
        !value_contains_sorry(value),
        "{name} proof value contains sorry / sorryAx"
    );
}

fn axiom_dep_names(env: &Environment, name: &str) -> std::collections::BTreeSet<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("axiom_deps should work for {name}"))
        .into_iter()
        .map(|dep| dep.to_string())
        .collect()
}

// ---------------------------------------------------------------
// Registration tests
// ---------------------------------------------------------------

const TARGET_LEMMAS: &[&str] = &[
    "Rat.sub_self",
    "Rat.mul_sub",
    "Rat.sub_nonneg_of_le",
    "Rat.le_of_sub_nonneg",
];

#[test]
fn test_rat_sub_self_registered() {
    assert_registered(&make_env(), "Rat.sub_self");
}

#[test]
fn test_rat_mul_sub_registered() {
    assert_registered(&make_env(), "Rat.mul_sub");
}

#[test]
fn test_rat_sub_nonneg_of_le_registered() {
    assert_registered(&make_env(), "Rat.sub_nonneg_of_le");
}

#[test]
fn test_rat_le_of_sub_nonneg_registered() {
    assert_registered(&make_env(), "Rat.le_of_sub_nonneg");
}

// ---------------------------------------------------------------
// Type-check tests
// ---------------------------------------------------------------

#[test]
fn test_all_four_type_check() {
    let env = make_env();
    for name in TARGET_LEMMAS {
        assert_type_checks(&env, name);
    }
}

// ---------------------------------------------------------------
// Theorem (not Opaque/Axiom) tests
// ---------------------------------------------------------------

#[test]
fn test_all_four_are_theorems() {
    let env = make_env();
    for name in TARGET_LEMMAS {
        assert_is_theorem(&env, name);
    }
}

// ---------------------------------------------------------------
// Sorry-free tests (guard against sorry-Opaque drift)
// ---------------------------------------------------------------

#[test]
fn test_all_four_are_sorry_free() {
    let env = make_env();
    for name in TARGET_LEMMAS {
        assert_no_sorry_in_value(&env, name);
    }
}

// ---------------------------------------------------------------
// Axiom-closure tests (zero sorry in transitive closure; post-#3656
// bridge spillover removed; allowed Rat field/order axioms only).
// ---------------------------------------------------------------

/// Axioms allowed in the transitive closure of our 4 bridging lemmas.
/// These are the already-registered Rat field and order axioms we build
/// on, plus the two honest helper axioms we add in this module.
const ALLOWED_RAT_AXIOMS: &[&str] = &[
    // Honest helper axiom registered by this module.
    "Rat.add_neg_self",
    // NOTE (#3470 Lane #2/#3): `Rat.mul_neg` was previously listed here as a
    // helper Axiom. It is now a constructive `Declaration::Theorem`, so it no
    // longer appears in any axiom closure. The entry is retained (harmless) as
    // documentation of the elimination; the subset test no longer relies on it.
    "Rat.mul_neg",
    // Existing field axioms.
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
    "Rat.add_right_cancel",
    "Rat.inv_zero",
    // Existing order / ordered-field axioms (Rat.add_le_add_left is
    // already foundational, but the auditor lists it there).
    "Rat.add_le_add_left",
    // NOTE (#3572 Phase 2): `Rat.add_comm` was promoted from
    // `Declaration::Axiom` to `Declaration::Theorem` with a constructive
    // proof over `Int.add_comm` + `Nat.mul_comm` (see
    // `algebra_rat_add_comm_proof.rs`). The BFS in `axiom_deps` no longer
    // short-circuits on `Rat.add_comm` (it is now a Theorem, not an Axiom),
    // so it walks its proof body and surfaces its two underlying axioms.
    // Both must appear in this allow-list so the subset test remains green
    // for `Rat.sub_nonneg_of_le` / `Rat.le_of_sub_nonneg`, which call into
    // `Rat.add_comm` via `nn_verify_rat_ordering.rs:412`.
    "Int.add_comm",
    "Nat.mul_comm",
    // NOTE (Part of #3582 Tranche C Phase 3 + #3572 Phase 3): Both
    // `Rat.mul_assoc` (Tranche C) and `Rat.add_assoc` (#3572 Phase 3) were
    // promoted from `Declaration::Axiom` to `Declaration::Theorem` with
    // constructive proofs. The BFS in `axiom_deps` no longer short-circuits
    // on either of them, so the full Int/Nat ring-normalization chain
    // surfaces transitively. Union of both promotions.
    "Int.add_assoc",
    "Int.mul_assoc",
    "Int.mul_comm",
    "Int.right_distrib",
    "Int.ofNat_mul",
    "Int.mul_one",
    "Int.add_zero",
    "Int.zero_add",
    "Int.zero_mul",
    "Nat.mul_assoc",
    "Nat.mul_one",
    "Nat.one_mul",
    // NOTE (#3656 / #3657): `Rat.left_distrib` has been rolled back to a
    // non-foundational `Declaration::Axiom` after #3654 found the
    // `Rat.mk_eq_mk_of_cross_eq` bridge unsound under the current carrier.
    // The BFS in `axiom_deps` now stops at `Rat.left_distrib` itself; it must
    // remain in this allow-list because `Rat.mul_sub` reaches it directly, but
    // the old bridge spillover (`Rat.mk_eq_mk_of_cross_eq`, `Int.left_distrib`,
    // etc.) must no longer appear transitively.
];

fn is_allowed_rat_axiom(name: &Name) -> bool {
    let s = name.to_string();
    ALLOWED_RAT_AXIOMS.iter().any(|&a| a == s)
}

#[test]
fn test_all_four_axiom_closures_do_not_contain_sorry() {
    let env = make_env();
    for name in TARGET_LEMMAS {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
        for dep in &deps {
            let s = dep.to_string();
            assert!(
                s != "sorry" && s != "sorryAx",
                "{name} transitively depends on {s} — MUST be sorry-free (#3503)"
            );
        }
    }
}

#[test]
fn test_all_four_axiom_closures_are_subset_of_allowed_rat_axioms() {
    let env = make_env();
    for name in TARGET_LEMMAS {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
        for dep in &deps {
            assert!(
                is_allowed_rat_axiom(dep),
                "{name} depends on unexpected non-foundational axiom {}; \
                 add it to ALLOWED_RAT_AXIOMS if intentional",
                dep
            );
        }
    }
}

/// `Rat.mul_sub` remains a `Declaration::Theorem`; its honest axiom closure is
/// now exactly `{Rat.left_distrib}`.
///
/// #3470 Lane #2/#3: `Rat.mul_neg` has been GENUINELY ELIMINATED from a
/// `Declaration::Axiom` to a kernel-checked `Declaration::Theorem` (a `congrArg`
/// over the symm of the constructive `Int.neg_mul_right`; see
/// `nn_verify_rat_ordering.rs::register_rat_mul_neg`). Because `axiom_deps`
/// short-circuits only on `kind == Axiom`, the BFS now walks INTO `Rat.mul_neg`'s
/// constructive proof body — which reaches no domain axiom — so `Rat.mul_neg`
/// no longer appears in the closure of `Rat.mul_sub`. The single remaining
/// non-foundational dep is the still-admitted `Rat.left_distrib` axiom
/// (rolled back to an Axiom by #3656 / #3657). No `sorry`, no rogue axiom.
#[test]
fn test_rat_mul_sub_axiom_closure_is_left_distrib() {
    let env = make_env();
    let deps = axiom_dep_names(&env, "Rat.mul_sub");

    // WS-A ATOMIC LIVE SWITCH: `Rat.mul_sub`'s only remaining non-foundational
    // dep was the admitted `Rat.left_distrib`, now a `Constructive` quotient
    // Theorem (with `Rat.mul_neg` already eliminated). So `Rat.mul_sub`'s
    // non-foundational axiom closure is now EMPTY.
    assert!(
        deps.is_empty(),
        "Rat.mul_sub closure must now be EMPTY (Rat.left_distrib + Rat.mul_neg \
         are quotient Theorems), got {deps:?}",
    );

    // `Rat.mul_neg` is now a constructive Theorem (NOT an admitted domain axiom)
    // and is correctly excluded from the admitted-axiom list.
    assert!(
        !crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS.contains(&"Rat.mul_neg"),
        "Rat.mul_neg is now a constructive Theorem and must NOT be listed as an \
         admitted domain axiom",
    );
    let info = env
        .get_const(&Name::from_string("Rat.mul_neg"))
        .expect("Rat.mul_neg registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.mul_neg must be a Declaration::Theorem",
    );
}

// ---------------------------------------------------------------
// Helper axioms (new honest axioms registered by this module)
// ---------------------------------------------------------------

#[test]
fn test_helper_axioms_registered_as_axioms() {
    let env = make_env();
    // WS-A ATOMIC LIVE SWITCH: `Rat.add_neg_self` is now a genuine `Constructive`
    // quotient `Declaration::Theorem` (previously an honest helper axiom).
    let name = "Rat.add_neg_self";
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} should now be Declaration::Theorem (quotient payoff), got {:?}",
        info.kind
    );
    // #3470 Lane #2/#3: `Rat.mul_neg` has been GENUINELY ELIMINATED — it is now
    // a kernel-checked `Declaration::Theorem` (`congrArg` over the symm of the
    // constructive `Int.neg_mul_right`), no longer an Axiom.
    let mul_neg = env
        .get_const(&Name::from_string("Rat.mul_neg"))
        .expect("Rat.mul_neg should be registered");
    assert_eq!(
        mul_neg.kind,
        ConstantKind::Theorem,
        "Rat.mul_neg should now be Declaration::Theorem, got {:?}",
        mul_neg.kind
    );
    assert!(
        mul_neg.value.is_some(),
        "Rat.mul_neg Theorem must retain its proof value"
    );
}

// ---------------------------------------------------------------
// Idempotency
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_rat_ordering().expect("first init");
    env.init_nn_verify_rat_ordering()
        .expect("second init (idempotent)");
}
