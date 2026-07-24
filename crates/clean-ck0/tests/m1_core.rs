// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! M1 decision-core targeted tests (design §5): whnf (β/δ/ζ/proj/native-Nat),
//! def_eq (reflexivity, function-η, structure-η, proof-irrelevance side
//! condition, Quot ι, budget-as-Err), and infer/check.
//!
//! Every `Term` is built through the validation chokepoint (the only public way
//! to obtain one) from a `RawExpr` tree, so the tests also exercise `validate`.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    is_def_eq, BigNat, Budget, BudgetError, Env, InferError, MinimalEnv, Name, QuotKind, RawExpr,
    RawLevel, RawLit, Term, Transparency,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

// ---- RawExpr builders ----

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
fn r_const_lvls(name: &str, arity: usize) -> RawExpr {
    RawExpr::Const(n(name), vec![RawLevel::Zero; arity])
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter().fold(f, r_app)
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_let(ty: RawExpr, val: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Let(Box::new(ty), Box::new(val), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn r_nat(v: u64) -> RawExpr {
    RawExpr::Lit(RawLit::Nat(BigNat::from_u64(v)))
}
fn r_proj(struct_name: &str, idx: u32, e: RawExpr) -> RawExpr {
    RawExpr::Proj(n(struct_name), idx, Box::new(e))
}

/// Validate a closed raw term against `env`.
fn v(env: &dyn Env, raw: &RawExpr) -> Term {
    Term::validate_closed(env, raw).expect("term validates")
}

// ---- the env ----

/// Nat / Bool / String type formers, Nat ctors+ops, Bool ctors, Quot built-ins.
/// All declared types are built from `RawExpr` (non-dependent arrows are Pis
/// whose codomain ignores the binder).
fn base_env() -> MinimalEnv {
    // type-former env (just enough to validate `Nat`/`Bool` consts in types).
    let formers = MinimalEnv::new()
        .with_const_typed(n("Nat"), 0, v(&MinimalEnv::new(), &r_sort(1)))
        .with_const_typed(n("Bool"), 0, v(&MinimalEnv::new(), &r_sort(1)))
        .with_const_typed(n("String"), 0, v(&MinimalEnv::new(), &r_sort(1)));
    // Precompute all declared types (validated against `formers`) before moving
    // `formers` into the chained builder.
    let nat_t = v(&formers, &r_const("Nat"));
    let bool_t = v(&formers, &r_const("Bool"));
    let succ_t = v(&formers, &r_pi(r_const("Nat"), r_const("Nat")));
    let add_t = v(
        &formers,
        &r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat"))),
    );
    let mul_t = add_t.clone();
    let beq_t = v(
        &formers,
        &r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Bool"))),
    );
    let mut env = formers
        .with_const_typed(n("Nat.zero"), 0, nat_t)
        .with_const_typed(n("Nat.succ"), 0, succ_t)
        .with_const_typed(n("Nat.add"), 0, add_t)
        .with_const_typed(n("Nat.mul"), 0, mul_t)
        .with_const_typed(n("Nat.beq"), 0, beq_t)
        .with_const_typed(n("Bool.true"), 0, bool_t.clone())
        .with_const_typed(n("Bool.false"), 0, bool_t);
    env = env
        .with_quot(n("Quot"), 1, QuotKind::Type)
        .with_quot(n("Quot.mk"), 1, QuotKind::Mk)
        .with_quot(n("Quot.lift"), 2, QuotKind::Lift)
        .with_quot(n("Quot.ind"), 1, QuotKind::Ind);
    env
}

// helpers operating on Terms
fn whnf1(env: &dyn Env, t: &Term) -> Term {
    let mut b = Budget::default_budget();
    clean_ck0::whnf(env, t, &mut b).expect("whnf ok")
}
fn deq(env: &dyn Env, a: &Term, b: &Term) -> bool {
    let mut bud = Budget::default_budget();
    is_def_eq(env, a, b, &mut bud).expect("def_eq within budget")
}

// ============================ tests ============================

#[test]
fn test_whnf_beta() {
    let env = base_env();
    let applied = v(
        &env,
        &r_app(r_lam(r_const("Nat"), r_bvar(0)), r_const("Nat.zero")),
    );
    let zero = v(&env, &r_const("Nat.zero"));
    assert_eq!(whnf1(&env, &applied), zero);
}

#[test]
fn test_whnf_zeta_let() {
    let env = base_env();
    let t = v(&env, &r_let(r_const("Nat"), r_const("Nat.zero"), r_bvar(0)));
    let zero = v(&env, &r_const("Nat.zero"));
    assert_eq!(whnf1(&env, &t), zero);
}

#[test]
fn test_whnf_delta_transparent_only() {
    let mut env = base_env();
    let natc = v(&env, &r_const("Nat"));
    let zero = v(&env, &r_const("Nat.zero"));
    env = env
        .with_def(
            n("foo"),
            0,
            natc.clone(),
            zero.clone(),
            Transparency::Transparent,
        )
        .with_def(n("bar"), 0, natc, zero.clone(), Transparency::Opaque);
    let foo = v(&env, &r_const("foo"));
    let bar = v(&env, &r_const("bar"));
    assert_eq!(whnf1(&env, &foo), zero, "transparent unfolds");
    assert_eq!(whnf1(&env, &bar), bar, "opaque stays stuck");
}

#[test]
fn test_whnf_native_nat_ops() {
    let env = base_env();
    assert_eq!(
        whnf1(&env, &v(&env, &r_app(r_const("Nat.succ"), r_nat(2)))),
        v(&env, &r_nat(3))
    );
    assert_eq!(
        whnf1(
            &env,
            &v(&env, &r_apps(r_const("Nat.add"), vec![r_nat(2), r_nat(3)]))
        ),
        v(&env, &r_nat(5))
    );
    assert_eq!(
        whnf1(
            &env,
            &v(&env, &r_apps(r_const("Nat.mul"), vec![r_nat(4), r_nat(5)]))
        ),
        v(&env, &r_nat(20))
    );
}

#[test]
fn test_whnf_native_nat_beq_to_bool() {
    let env = base_env();
    assert_eq!(
        whnf1(
            &env,
            &v(&env, &r_apps(r_const("Nat.beq"), vec![r_nat(3), r_nat(3)]))
        ),
        v(&env, &r_const("Bool.true"))
    );
    assert_eq!(
        whnf1(
            &env,
            &v(&env, &r_apps(r_const("Nat.beq"), vec![r_nat(3), r_nat(4)]))
        ),
        v(&env, &r_const("Bool.false"))
    );
}

#[test]
fn test_whnf_proj_of_constructor() {
    let mut env = base_env();
    env = env
        .with_const_typed(n("Prod"), 2, v(&base_env(), &r_sort(1)))
        .with_constructor(n("Prod.mk"), 2, v(&base_env(), &r_sort(1)), 2, 2);
    // Prod.mk Nat Nat 7 9
    let val = r_apps(
        r_const_lvls("Prod.mk", 2),
        vec![r_const("Nat"), r_const("Nat"), r_nat(7), r_nat(9)],
    );
    let p0 = v(&env, &r_proj("Prod", 0, val.clone()));
    let p1 = v(&env, &r_proj("Prod", 1, val));
    assert_eq!(whnf1(&env, &p0), v(&env, &r_nat(7)));
    assert_eq!(whnf1(&env, &p1), v(&env, &r_nat(9)));
}

#[test]
fn test_def_eq_reflexivity() {
    let env = base_env();
    let t = v(
        &env,
        &r_lam(r_const("Nat"), r_app(r_const("Nat.succ"), r_bvar(0))),
    );
    assert!(deq(&env, &t, &t.clone()));
}

#[test]
fn test_def_eq_symmetry_and_transitivity() {
    let env = base_env();
    let a = v(&env, &r_apps(r_const("Nat.add"), vec![r_nat(1), r_nat(4)]));
    let b = v(&env, &r_nat(5));
    let c = v(&env, &r_apps(r_const("Nat.add"), vec![r_nat(2), r_nat(3)]));
    assert!(deq(&env, &a, &b));
    assert!(deq(&env, &b, &a), "symmetry");
    assert!(deq(&env, &b, &c));
    assert!(deq(&env, &a, &c), "transitivity");
}

#[test]
fn test_def_eq_unequal_is_ok_false_not_err() {
    let env = base_env();
    let mut bud = Budget::default_budget();
    let r = is_def_eq(&env, &v(&env, &r_nat(2)), &v(&env, &r_nat(3)), &mut bud);
    assert_eq!(r, Ok(false));
}

#[test]
fn test_def_eq_function_eta() {
    let env = base_env();
    let succ = v(&env, &r_const("Nat.succ"));
    let lam = v(
        &env,
        &r_lam(r_const("Nat"), r_app(r_const("Nat.succ"), r_bvar(0))),
    );
    assert!(deq(&env, &lam, &succ), "λx. succ x ≡ succ");
    assert!(deq(&env, &succ, &lam), "η symmetric");
}

#[test]
fn test_def_eq_structure_eta() {
    let mut env = base_env();
    // Prod : Type -> Type -> Type
    let prod_ty = r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1)));
    // Prod.mk : (α β : Type) -> α -> β -> Prod α β
    let mk_ty = r_pi(
        r_sort(1),
        r_pi(
            r_sort(1),
            r_pi(
                r_bvar(1),
                r_pi(
                    r_bvar(1),
                    r_apps(r_const_lvls("Prod", 0), vec![r_bvar(3), r_bvar(2)]),
                ),
            ),
        ),
    );
    env = env
        .with_const_typed(n("Prod"), 0, v(&base_env(), &prod_ty))
        .with_structure(n("Prod"), n("Prod.mk"), 2, 2);
    let mk_ty_term = v(&env, &mk_ty);
    env = env.with_constructor(n("Prod.mk"), 0, mk_ty_term, 2, 2);
    // s : Prod Nat Nat (opaque const)
    let s_ty = r_apps(r_const("Prod"), vec![r_const("Nat"), r_const("Nat")]);
    let s_ty_term = v(&env, &s_ty);
    env = env.with_const_typed(n("s"), 0, s_ty_term);
    let s = v(&env, &r_const("s"));
    let expanded = v(
        &env,
        &r_apps(
            r_const_lvls("Prod.mk", 0),
            vec![
                r_const("Nat"),
                r_const("Nat"),
                r_proj("Prod", 0, r_const("s")),
                r_proj("Prod", 1, r_const("s")),
            ],
        ),
    );
    assert!(deq(&env, &s, &expanded), "s ≡ Prod.mk Nat Nat s.0 s.1");
}

#[test]
fn test_proof_irrelevance_same_prop() {
    let env0 = base_env().with_const_typed(n("P"), 0, v(&base_env(), &r_sort(0)));
    let p_ty = v(&env0, &r_const("P"));
    let env = env0
        .with_const_typed(n("p1"), 0, p_ty.clone())
        .with_const_typed(n("p2"), 0, p_ty);
    let p1 = v(&env, &r_const("p1"));
    let p2 = v(&env, &r_const("p2"));
    assert!(deq(&env, &p1, &p2), "two proofs of P are def-eq");
}

#[test]
fn test_proof_irrelevance_different_prop_not_bridged() {
    let env0 = base_env()
        .with_const_typed(n("P"), 0, v(&base_env(), &r_sort(0)))
        .with_const_typed(n("Q"), 0, v(&base_env(), &r_sort(0)));
    let p_ty = v(&env0, &r_const("P"));
    let q_ty = v(&env0, &r_const("Q"));
    let env = env0
        .with_const_typed(n("p1"), 0, p_ty)
        .with_const_typed(n("q1"), 0, q_ty);
    let p1 = v(&env, &r_const("p1"));
    let q1 = v(&env, &r_const("q1"));
    assert!(
        !deq(&env, &p1, &q1),
        "proofs of different Props not bridged"
    );
}

#[test]
fn test_proof_irrelevance_non_prop_not_bridged() {
    let env = base_env();
    let a = v(&env, &r_const("Nat.zero"));
    let b = v(&env, &r_nat(1));
    assert!(!deq(&env, &a, &b), "distinct Nat (Type) not bridged");
}

#[test]
fn test_quot_lift_iota() {
    let mut env = base_env();
    for c in ["a0", "r0", "b0", "f0", "h0", "x0"] {
        env = env.with_const_typed(n(c), 0, v(&base_env(), &r_sort(0)));
    }
    let mk_app = r_apps(
        r_const_lvls("Quot.mk", 1),
        vec![r_const("a0"), r_const("r0"), r_const("x0")],
    );
    let lift_app = r_apps(
        r_const_lvls("Quot.lift", 2),
        vec![
            r_const("a0"),
            r_const("r0"),
            r_const("b0"),
            r_const("f0"),
            r_const("h0"),
            mk_app,
        ],
    );
    let expected = r_app(r_const("f0"), r_const("x0"));
    assert!(
        deq(&env, &v(&env, &lift_app), &v(&env, &expected)),
        "Quot.lift f h (Quot.mk a) ≡ f a"
    );
}

#[test]
fn test_budget_exhaustion_returns_err() {
    let env = base_env();
    let big = v(
        &env,
        &r_apps(r_const("Nat.add"), vec![r_nat(1000), r_nat(1000)]),
    );
    let target = v(&env, &r_nat(2000));
    let mut bud = Budget::new(3);
    let r = is_def_eq(&env, &big, &target, &mut bud);
    assert_eq!(r, Err(BudgetError::OutOfBudget));
}

// ---- infer / check ----

#[test]
fn test_infer_sort_of_sort() {
    let env = base_env();
    let s0 = v(&env, &r_sort(0));
    let ty = clean_ck0::infer(&env, &s0, &mut Budget::default_budget()).expect("infer");
    assert_eq!(ty, v(&env, &r_sort(1)));
}

#[test]
fn test_infer_lam_is_pi() {
    let env = base_env();
    let id = v(&env, &r_lam(r_const("Nat"), r_bvar(0)));
    let ty = clean_ck0::infer(&env, &id, &mut Budget::default_budget()).expect("infer");
    let expected = v(&env, &r_pi(r_const("Nat"), r_const("Nat")));
    assert_eq!(ty, expected);
}

#[test]
fn test_infer_app_and_lit() {
    let env = base_env();
    let t = v(&env, &r_app(r_const("Nat.succ"), r_const("Nat.zero")));
    let ty = clean_ck0::infer(&env, &t, &mut Budget::default_budget()).expect("infer");
    assert_eq!(ty, v(&env, &r_const("Nat")));
    let lit_ty =
        clean_ck0::infer(&env, &v(&env, &r_nat(42)), &mut Budget::default_budget()).expect("infer");
    assert_eq!(lit_ty, v(&env, &r_const("Nat")));
}

#[test]
fn test_check_succeeds_and_rejects() {
    let env = base_env();
    let t = v(&env, &r_app(r_const("Nat.succ"), r_const("Nat.zero")));
    assert!(clean_ck0::check(
        &env,
        &t,
        &v(&env, &r_const("Nat")),
        &mut Budget::default_budget()
    )
    .is_ok());
    assert!(clean_ck0::check(
        &env,
        &t,
        &v(&env, &r_const("Bool")),
        &mut Budget::default_budget()
    )
    .is_err());
}

#[test]
fn test_infer_elim_without_recursor_is_unknown_not_fabricated() {
    // M2: Elim typing reads the env's derived recursor type. With an inductive
    // registered but no recursor (the M1 placeholder env), infer reports
    // UnknownConst — a clear reject, never a fabricated type.
    let env = base_env().with_inductive(n("Nat"), 0, false);
    let raw = RawExpr::Elim(n("Nat"), RawLevel::Zero, vec![]);
    let t = Term::validate_closed(&env, &raw).expect("elim validates");
    let r = clean_ck0::infer(&env, &t, &mut Budget::default_budget());
    assert_eq!(r, Err(InferError::UnknownConst { name: n("Nat") }));
}
