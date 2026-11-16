// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integrity controls for finite-fragment certificates: statement identity,
//! reachable-set mutations and protected vocabulary.

use super::edgegate_cert;
use clean_kernel::env::{Declaration, Environment, ProofQuality};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_tla::finite::{
    encode_finite, register_ty_cert_safety_finite, FiniteError, FiniteMachine,
};
use clean_tla::ty_cert::{self, TyCert};

// ── the α-gate: `_assumed` can NEVER look like the finite conclusion ───────

#[test]
fn test_assumed_product_never_passes_alpha_gate() {
    // Register the 1-variable `_assumed` product (three Pi-BOUND hypotheses)
    // and α-compare its type against the independently recomputed bare
    // conclusion — the exact check the Certified gate must run. They MUST
    // differ; ProofQuality does NOT discriminate (both are Constructive).
    let acc = TyCert {
        schema: "ty.cert/v1".into(),
        verdict: "inductive-safety-safe".into(),
        spec_src: "---- MODULE Accumulator ----\n\
                   EXTENDS Integers\n\
                   VARIABLE x\n\
                   Init == x = 0\n\
                   Next == x' = x + 1\n\
                   Safety == x >= 0\n\
                   ====\n"
            .into(),
        init: Some("Init".into()),
        next: Some("Next".into()),
        invariants: vec!["Safety".into()],
        invariant_j_tla: "x >= 0".into(),
        var_sorts: vec![("x".into(), "Int".into())],
        constants: vec![],
        ay_proof_obligations: vec![],
    };
    let enc = ty_cert::encode_cert(&acc).expect("encode");
    let conclusion = ty_cert::conclusion_ty(&enc.init, &enc.next, &enc.safety);

    let mut env = Environment::new();
    ty_cert::register_ty_cert_safety_assumed(&mut env, "TYAccAssumedGate", &enc)
        .expect("assumed registers");
    let assumed = env
        .get_const(&Name::from_string("TYAccAssumedGate"))
        .expect("assumed registered");
    assert_ne!(
        assumed.type_, conclusion,
        "the α-exact type comparison MUST reject the _assumed product \
         (its type carries three extra leading Pi-hypotheses)"
    );
    // …while ProofQuality alone would NOT reject it:
    assert_eq!(
        env.proof_quality(&Name::from_string("TYAccAssumedGate"))
            .expect("quality"),
        ProofQuality::Constructive,
        "Constructive does not discriminate _assumed — the TYPE does"
    );

    // The closed product DOES pass the same comparison.
    let mut env2 = Environment::with_prelude();
    ty_cert::register_ty_cert_safety_closed(&mut env2, "TYAccClosedGate", &enc)
        .expect("closed registers");
    let closed = env2
        .get_const(&Name::from_string("TYAccClosedGate"))
        .expect("closed registered");
    assert_eq!(closed.type_, conclusion, "closed product IS the conclusion");
}

// ── mutation battery: tampered reachable sets are caught BY THE KERNEL ─────

fn register_tampered(
    mutate: impl FnOnce(&mut Vec<Vec<i64>>),
    thm: &str,
) -> (Environment, Result<(), FiniteError>) {
    let m = FiniteMachine::from_cert(&edgegate_cert(0)).expect("machine");
    let mut x = m.explore().expect("explore");
    mutate(&mut x.reachable);
    let mut env = Environment::with_prelude();
    let r = encode_finite(&m, &x, thm)
        .and_then(|enc| clean_tla::finite::register_finite_encoded(&mut env, &enc).map(|_| ()));
    (env, r)
}

#[test]
fn test_mutation_dropped_successor_rejected_by_kernel() {
    // J = {init} only: the closure leaf `memB(step init)` evaluates FALSE, so
    // the rfl leg cannot kernel-check. Caught by the kernel, fail closed.
    let (env, r) = register_tampered(|reach| reach.truncate(1), "TYMutDrop");
    assert!(r.is_err(), "dropped successor must be rejected");
    assert!(env.get_const(&Name::from_string("TYMutDrop")).is_none());
    assert!(env
        .get_const(&Name::from_string("TYMutDrop_sound"))
        .is_none());
    // ATOMICITY: registration is staged; the earlier legs (the checker and the
    // rfl leg) must NOT survive a failed product in the caller's env.
    assert!(env
        .get_const(&Name::from_string("TYMutDrop_check"))
        .is_none());
    assert!(env
        .get_const(&Name::from_string("TYMutDrop_check_eq_true"))
        .is_none());
}

#[test]
fn test_mutation_injected_unsafe_state_rejected_by_kernel() {
    // Inject (granted=0, decision=1): closed under the actions but UNSAFE, so
    // the safety leaf evaluates FALSE and the rfl leg fails.
    let (env, r) = register_tampered(|reach| reach.push(vec![0, 1]), "TYMutUnsafe");
    assert!(r.is_err(), "unsafe member of J must be rejected");
    assert!(env.get_const(&Name::from_string("TYMutUnsafe")).is_none());
    assert!(
        env.get_const(&Name::from_string("TYMutUnsafe_check"))
            .is_none(),
        "atomic registration: no leg survives a failed product"
    );
}

#[test]
fn test_mutation_swapped_state_value_rejected_by_kernel() {
    // Replace (1,1) by (1,0): Grant's successor (1,1) is no longer in J, so
    // the closure leaf evaluates FALSE and the rfl leg fails.
    let (env, r) = register_tampered(
        |reach| {
            assert_eq!(reach[1], vec![1, 1]);
            reach[1] = vec![1, 0];
        },
        "TYMutSwap",
    );
    assert!(r.is_err(), "non-closed J must be rejected");
    assert!(env.get_const(&Name::from_string("TYMutSwap")).is_none());
    assert!(
        env.get_const(&Name::from_string("TYMutSwap_check"))
            .is_none(),
        "atomic registration: no leg survives a failed product"
    );
}

#[test]
fn test_mutation_safe_closed_superset_is_sound_and_accepted() {
    // Sanity inverse: ADDING a safe, closed extra state (granted=1,decision=0)
    // keeps every check true — J need not be exactly the reachable set, only
    // closed and safe. The kernel accepts; soundness is unaffected.
    let (env, r) = register_tampered(|reach| reach.push(vec![1, 0]), "TYMutSuperset");
    assert!(
        r.is_ok(),
        "a safe closed superset J is legitimately accepted: {r:?}"
    );
    assert!(env.get_const(&Name::from_string("TYMutSuperset")).is_some());
}

// ── blessed-vocabulary squats ──────────────────────────────────────────────

#[test]
fn test_tlafin_vocabulary_squat_refused() {
    let mut env = Environment::with_prelude();
    // A bogus TLAfin.cond (`λ c t e, t` — ignores the condition) with the
    // RIGHT type: building on it would change the meaning of every statement
    // mentioning it. Must be refused.
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
    let bogus = Expr::lam(
        BinderInfo::Default,
        bool_c.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_c.clone(),
            Expr::lam(BinderInfo::Default, nat_c.clone(), Expr::bvar(1)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("TLAfin.cond"),
        level_params: vec![],
        type_: Expr::arrow(
            bool_c,
            Expr::arrow(nat_c.clone(), Expr::arrow(nat_c.clone(), nat_c)),
        ),
        value: bogus,
        is_reducible: true,
    })
    .expect("bogus TLAfin.cond registers as a plain definition");

    let err = register_ty_cert_safety_finite(&mut env, "TYVocabSquat", &edgegate_cert(0))
        .expect_err("squatted TLAfin vocabulary must be refused");
    assert!(
        matches!(&err, FiniteError::VocabularySquatted { name } if name == "TLAfin.cond"),
        "got {err}"
    );
    assert!(env.get_const(&Name::from_string("TYVocabSquat")).is_none());
}

#[test]
fn test_tlasem_keystone_squat_refused() {
    let mut env = Environment::with_prelude();
    // Squat the keystone NAME with a trivially-true theorem of a DIFFERENT
    // statement. The finite lane's integrity check must refuse to build on it.
    let nat_c = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::nat_lit(0);
    let eq00 = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_c.clone(), zero.clone(), zero.clone()],
    );
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("TLAsem.InductiveInvariantSound"),
        level_params: vec![],
        type_: eq00,
        value: Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat_c, zero],
        ),
    })
    .expect("squatted keystone registers as a plain theorem");

    let err = register_ty_cert_safety_finite(&mut env, "TYKeystoneSquat", &edgegate_cert(0))
        .expect_err("squatted keystone must be refused");
    assert!(
        matches!(&err, FiniteError::VocabularySquatted { name } if name == "TLAsem.InductiveInvariantSound"),
        "got {err}"
    );
    assert!(env
        .get_const(&Name::from_string("TYKeystoneSquat"))
        .is_none());
}
