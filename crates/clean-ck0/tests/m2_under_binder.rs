// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! M2 under-binder typing test (design §5.2 + the M1 gap closure): with `infer`
//! extended to a local typing context, `def_eq` can run proof-irrelevance and
//! structure-η **under binders**. This test exercises the proof-irrelevance leg
//! under a `λ` binder, which the M1 implementation could only do at the top
//! level (it gated proof-irrel on `ctx.is_empty()`).

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{is_def_eq, Budget, MinimalEnv, Name, RawExpr, RawLevel, Term, Transparency};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}
fn r_sort(level: u32) -> RawExpr {
    let mut l = RawLevel::Zero;
    for _ in 0..level {
        l = RawLevel::Succ(Box::new(l));
    }
    RawExpr::Sort(l)
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}

/// Env: `P : Prop`, two distinct proofs `p q : P`, and a base type `T : Type`.
fn env_with_prop() -> MinimalEnv {
    let bootstrap = MinimalEnv::new();
    // P : Prop
    let p_ty = Term::validate_closed(&bootstrap, &r_sort(0)).expect("Prop");
    // T : Type 0
    let t_ty = Term::validate_closed(&bootstrap, &r_sort(1)).expect("Type");
    let mut env = MinimalEnv::new()
        .with_const_typed(n("P"), 0, p_ty)
        .with_const_typed(n("T"), 0, t_ty);
    // p : P, q : P  (two distinct opaque proofs of the same Prop).
    let p_t = Term::validate_closed(&env, &r_const("P")).expect("P type");
    env = env
        .with_def(
            n("p"),
            0,
            p_t.clone(),
            // body irrelevant (opaque); register a type only.
            p_t.clone(),
            Transparency::Opaque,
        )
        .with_def(n("q"), 0, p_t.clone(), p_t.clone(), Transparency::Opaque);
    env
}

#[test]
fn test_proof_irrel_fires_under_binder() {
    let env = env_with_prop();
    // λ (x : T). p   vs   λ (x : T). q
    // These are equal ONLY via proof-irrelevance applied to `p` and `q` UNDER
    // the lambda binder (both have type P : Prop). At M1 this was skipped under
    // binders; at M2 it must fire.
    let lam_p = Term::validate_closed(&env, &r_lam(r_const("T"), r_const("p"))).expect("λx.p");
    let lam_q = Term::validate_closed(&env, &r_lam(r_const("T"), r_const("q"))).expect("λx.q");
    let mut budget = Budget::default_budget();
    let eq = is_def_eq(&env, &lam_p, &lam_q, &mut budget).expect("def_eq");
    assert!(
        eq,
        "proof-irrelevance must equate λx.p and λx.q (p,q : P : Prop) under the binder"
    );
}

#[test]
fn test_proof_irrel_does_not_bridge_non_prop_under_binder() {
    // Two distinct non-Prop constants under a binder must NOT be equated.
    let bootstrap = MinimalEnv::new();
    let t_ty = Term::validate_closed(&bootstrap, &r_sort(1)).expect("Type");
    let mut env = MinimalEnv::new().with_const_typed(n("T"), 0, t_ty);
    let t_t = Term::validate_closed(&env, &r_const("T")).expect("T type");
    env = env
        .with_def(n("a"), 0, t_t.clone(), t_t.clone(), Transparency::Opaque)
        .with_def(n("b"), 0, t_t.clone(), t_t.clone(), Transparency::Opaque);
    let lam_a = Term::validate_closed(&env, &r_lam(r_const("T"), r_const("a"))).expect("λx.a");
    let lam_b = Term::validate_closed(&env, &r_lam(r_const("T"), r_const("b"))).expect("λx.b");
    let mut budget = Budget::default_budget();
    let eq = is_def_eq(&env, &lam_a, &lam_b, &mut budget).expect("def_eq");
    assert!(
        !eq,
        "non-Prop a,b : T must NOT be equated under the binder (proof-irrel is Prop-gated)"
    );
}
