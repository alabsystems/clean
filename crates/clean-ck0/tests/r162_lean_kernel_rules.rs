// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three Lean kernel rules ck0 lacked until R162, each with a positive and a
//! negative control (`docs/DECISIONS.md` R162; found by the VF4 quorum re-check,
//! `crates/clean-olean/tests/vf4_chk_lia_quorum.rs`, where ck0 refused 246 of
//! the 905 declarations of `chk_LIA_sound`'s and the F1 certificates' cone):
//!
//! 1. **`Nat` literal ⇄ constructor.** `Nat.rec` on a literal major premise
//!    fires its ι-rule (`0` is `Nat.zero`, `n + 1` is `Nat.succ n`), and a
//!    literal is definitionally its constructor form; a literal never equals the
//!    other constructor, and a literal major of another inductive stays stuck.
//! 2. **An applied projection reduces.** `(Prod.fst (Prod.mk f a)) x ≡ f x`.
//! 3. **K-like reduction.** The eliminator of a K-target (`Eq`: in `Prop`, one
//!    constructor, no fields) on a VARIABLE major whose type is the
//!    constructor's (`h : zero = zero`) reduces as on `Eq.refl`; on a major of
//!    another type (`h : zero = succ zero`) it stays stuck.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, BigNat, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name, RawExpr,
    RawLevel, RawLit, Term,
};

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
fn r_prop() -> RawExpr {
    RawExpr::Sort(RawLevel::Zero)
}
fn r_sort_param(i: u32) -> RawExpr {
    RawExpr::Sort(RawLevel::Param(i))
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_const_p(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter().fold(f, r_app)
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn lparam(i: u32) -> RawLevel {
    RawLevel::Param(i)
}
fn lsucc(l: RawLevel) -> RawLevel {
    RawLevel::Succ(Box::new(l))
}

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

// ===========================================================================
// The standard Init inductives, with their REAL Lean signatures.
// ===========================================================================

/// `Bool : Type` with `false : Bool`, `true : Bool`.
/// `Nat : Type` with `zero : Nat`, `succ : Nat -> Nat`.
fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![
            Constructor {
                name: n("Nat.zero"),
                type_: vlvl(&b, &r_const("Nat"), 0),
            },
            Constructor {
                name: n("Nat.succ"),
                type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat")), 0),
            },
        ],
    }
}

/// `Eq.{u} {A : Sort u} (a : A) : A -> Prop` with `refl (a) : Eq a a`.
/// Built with num_params = 2 (A and a), matching the M2 fixture.
fn eq_decl() -> InductiveDecl {
    let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
    let ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(r_bvar(1), r_prop())));
    let refl_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_bvar(0),
            r_apps(
                r_const_p("Eq", vec![lparam(0)]),
                vec![r_bvar(1), r_bvar(0), r_bvar(0)],
            ),
        ),
    );
    InductiveDecl {
        name: n("Eq"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &ty, 1),
        constructors: vec![Constructor {
            name: n("Eq.refl"),
            type_: vlvl(&b, &refl_ty, 1),
        }],
    }
}

/// `And (a b : Prop) : Prop` with `intro : a -> b -> And a b`. num_params = 2.
fn prod_decl() -> InductiveDecl {
    let b = boot(&[("Prod", 2), ("Prod.mk", 2)]);
    // Prod : Sort u -> Sort v -> Sort (max 1 u v)
    let ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_sort_param(1),
            RawExpr::Sort(RawLevel::Max(
                Box::new(lsucc(RawLevel::Zero)),
                Box::new(RawLevel::Max(Box::new(lparam(0)), Box::new(lparam(1)))),
            )),
        ),
    );
    // mk : (A : Sort u) -> (B : Sort v) -> A -> B -> Prod A B
    let mk_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_sort_param(1),
            r_pi(
                r_bvar(1), // A
                r_pi(
                    r_bvar(1), // B
                    r_apps(
                        r_const_p("Prod", vec![lparam(0), lparam(1)]),
                        vec![r_bvar(3), r_bvar(2)],
                    ),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("Prod"),
        num_level_params: 2,
        num_params: 2,
        type_: vlvl(&b, &ty, 2),
        constructors: vec![Constructor {
            name: n("Prod.mk"),
            type_: vlvl(&b, &mk_ty, 2),
        }],
    }
}

// ---------------------------------------------------------------------------

fn env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, eq_decl()).expect("Eq admits");
    add_inductive(&mut env, prod_decl()).expect("Prod admits");
    env
}

fn lit(v: u64) -> RawExpr {
    RawExpr::Lit(RawLit::Nat(BigNat::from_u64(v)))
}
fn one() -> RawLevel {
    lsucc(RawLevel::Zero)
}
fn t(env: &MinimalEnv, raw: &RawExpr) -> Term {
    Term::validate(env, raw, 0, 0).expect("term validates")
}
fn def_eq(env: &MinimalEnv, a: &RawExpr, b: &RawExpr) -> bool {
    let mut budget = Budget::default_budget();
    clean_ck0::is_def_eq(env, &t(env, a), &t(env, b), &mut budget).expect("within budget")
}
/// `proof : ty` checks.
fn checks(env: &MinimalEnv, ty: &RawExpr, proof: &RawExpr) -> bool {
    let mut budget = Budget::default_budget();
    clean_ck0::check(env, &t(env, proof), &t(env, ty), &mut budget).is_ok()
}
fn eq_nat(a: RawExpr, b: RawExpr) -> RawExpr {
    r_apps(r_const_p("Eq", vec![one()]), vec![r_const("Nat"), a, b])
}
fn refl_nat(a: RawExpr) -> RawExpr {
    r_apps(r_const_p("Eq.refl", vec![one()]), vec![r_const("Nat"), a])
}
/// `Nat.rec (motive := fun _ => Nat) base (fun _ ih => succ ih) major`: `base + major`.
fn add_by_rec(base: RawExpr, major: RawExpr) -> RawExpr {
    r_apps(
        RawExpr::Elim(n("Nat"), one(), vec![]),
        vec![
            r_lam(r_const("Nat"), r_const("Nat")),
            base,
            r_lam(
                r_const("Nat"),
                r_lam(r_const("Nat"), r_app(r_const("Nat.succ"), r_bvar(0))),
            ),
            major,
        ],
    )
}

#[test]
fn nat_rec_fires_on_a_literal_major() {
    let env = env();
    assert!(def_eq(&env, &add_by_rec(lit(7), lit(3)), &lit(10)));
    assert!(
        !def_eq(&env, &add_by_rec(lit(7), lit(3)), &lit(11)),
        "control: 7 + 3 ≠ 11"
    );
    assert!(def_eq(&env, &add_by_rec(lit(7), lit(0)), &lit(7)));
    // As a theorem: `7 + 3 = 10 := rfl` checks; `= 11` does not.
    assert!(checks(
        &env,
        &eq_nat(add_by_rec(lit(7), lit(3)), lit(10)),
        &refl_nat(lit(10))
    ));
    assert!(!checks(
        &env,
        &eq_nat(add_by_rec(lit(7), lit(3)), lit(11)),
        &refl_nat(lit(11))
    ));
}

#[test]
fn a_literal_is_its_constructor_form() {
    let env = env();
    let succ = |e: RawExpr| r_app(r_const("Nat.succ"), e);
    assert!(def_eq(&env, &lit(0), &r_const("Nat.zero")));
    assert!(def_eq(&env, &lit(2), &succ(succ(r_const("Nat.zero")))));
    assert!(def_eq(&env, &succ(succ(r_const("Nat.zero"))), &lit(2)));
    assert!(
        !def_eq(&env, &lit(0), &succ(r_const("Nat.zero"))),
        "control: 0 ≠ succ 0"
    );
    assert!(
        !def_eq(&env, &lit(1), &r_const("Nat.zero")),
        "control: 1 ≠ zero"
    );
    assert!(
        !def_eq(&env, &lit(3), &succ(succ(r_const("Nat.zero")))),
        "control: 3 ≠ 2"
    );
}

#[test]
fn an_applied_projection_reduces() {
    let env = env();
    // p := Prod.mk (Nat → Nat) Nat Nat.succ 0;  (p.1) 4 ≡ 5, and ≢ 4.
    let p = r_apps(
        r_const_p("Prod.mk", vec![one(), one()]),
        vec![
            r_pi(r_const("Nat"), r_const("Nat")),
            r_const("Nat"),
            r_const("Nat.succ"),
            lit(0),
        ],
    );
    let applied = r_app(RawExpr::Proj(n("Prod"), 0, Box::new(p)), lit(4));
    assert!(def_eq(&env, &applied, &lit(5)));
    assert!(!def_eq(&env, &applied, &lit(4)), "control: succ 4 ≠ 4");
}

/// `fun (h : Eq Nat x y) => (Eq.refl Nat 5 : Eq Nat (Eq.rec (motive := fun _ _ =>
/// Nat) 5 h) 5)`, i.e. the theorem `∀ h : x = y, Eq.rec 5 h = 5`.
fn k_theorem(x: RawExpr, y: RawExpr) -> (RawExpr, RawExpr) {
    // Under the binder h: h = #0.
    // motive : (b : Nat) → Eq Nat x b → Sort 1, as `fun b _ => Nat`.
    let motive = r_lam(
        r_const("Nat"),
        r_lam(eq_nat(x.clone(), r_bvar(0)), r_const("Nat")),
    );
    let rec = r_apps(
        RawExpr::Elim(n("Eq"), one(), vec![one()]),
        vec![
            r_const("Nat"),
            x.clone(),
            motive,
            lit(5),
            y.clone(),
            r_bvar(0),
        ],
    );
    let ty = r_pi(eq_nat(x, y), eq_nat(rec, lit(5)));
    let proof = r_lam(r_bvar(99), refl_nat(lit(5)));
    (ty, proof)
}

#[test]
fn k_like_reduction_on_a_variable_major() {
    let env = env();
    let (ty, proof) = k_theorem(r_const("Nat.zero"), r_const("Nat.zero"));
    // The lambda's binder type is the Pi's domain.
    let RawExpr::Pi(_, dom, _) = &ty else {
        unreachable!()
    };
    let RawExpr::Lam(bi, _, body) = proof else {
        unreachable!()
    };
    let proof = RawExpr::Lam(bi, dom.clone(), body);
    assert!(
        checks(&env, &ty, &proof),
        "K: Eq.rec 5 h ≡ 5 for h : zero = zero"
    );

    // Control: h : zero = succ zero is not the constructor's type, so the
    // eliminator stays stuck and the proof is refused.
    let (ty, proof) = k_theorem(
        r_const("Nat.zero"),
        r_app(r_const("Nat.succ"), r_const("Nat.zero")),
    );
    let RawExpr::Pi(_, dom, _) = &ty else {
        unreachable!()
    };
    let RawExpr::Lam(bi, _, body) = proof else {
        unreachable!()
    };
    let proof = RawExpr::Lam(bi, dom.clone(), body);
    assert!(
        !checks(&env, &ty, &proof),
        "control: no K for h : zero = succ zero"
    );
}

fn env_with_nat_ops() -> MinimalEnv {
    let mut e = env();
    let nn = r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat")));
    for op in ["gcd", "land", "lor", "xor", "shiftLeft", "shiftRight"] {
        let ty = t(&e, &nn);
        e = e.with_const_typed(n(&format!("Nat.{op}")), 0, ty);
    }
    e
}

fn op(name: &str, a: u64, b: u64) -> RawExpr {
    r_apps(r_const(&format!("Nat.{name}")), vec![lit(a), lit(b)])
}

#[test]
fn the_rest_of_leans_native_nat_extensions_reduce() {
    let env = env_with_nat_ops();
    for (name, a, b, want, not) in [
        ("gcd", 12, 18, 6, 3),
        ("gcd", 0, 7, 7, 0),
        ("land", 6, 3, 2, 3),
        ("lor", 5, 3, 7, 6),
        ("xor", 5, 3, 6, 7),
        ("shiftLeft", 3, 4, 48, 12),
        ("shiftRight", 256, 4, 16, 64),
        ("shiftRight", 5, 70, 0, 1),
    ] {
        assert!(
            def_eq(&env, &op(name, a, b), &lit(want)),
            "Nat.{name} {a} {b} = {want}"
        );
        assert!(
            !def_eq(&env, &op(name, a, b), &lit(not)),
            "control: Nat.{name} {a} {b} ≠ {not}"
        );
    }
}

/// `let n : Nat := 3; (fun (h : n = 3) => h) (Eq.refl 3)`: the argument's type
/// `3 = 3` is the domain `n = 3` only when the body sees `n`'s value.
#[test]
fn a_let_body_is_typed_with_the_bound_value() {
    let env = env();
    let body = r_app(
        r_lam(eq_nat(r_bvar(0), lit(3)), r_bvar(0)),
        refl_nat(lit(3)),
    );
    let term = RawExpr::Let(
        Box::new(r_const("Nat")),
        Box::new(lit(3)),
        Box::new(body.clone()),
    );
    assert!(checks(&env, &eq_nat(lit(3), lit(3)), &term));
    // Control: the same body under `n := 4` is ill-typed.
    let bad = RawExpr::Let(Box::new(r_const("Nat")), Box::new(lit(4)), Box::new(body));
    let mut budget = Budget::default_budget();
    assert!(
        clean_ck0::infer(&env, &t(&env, &bad), &mut budget).is_err(),
        "control: (fun (h : 4 = 3) => h) (Eq.refl 3) does not type"
    );
}

/// `let x : Nat := v; 0` types only when `v : Nat`: the body never mentions `x`,
/// so typing the body with `v` substituted cannot catch an ill-typed `v`; the
/// annotation check does.
#[test]
fn a_let_value_must_have_its_annotated_type() {
    let env = env();
    let good = RawExpr::Let(Box::new(r_const("Nat")), Box::new(lit(3)), Box::new(lit(0)));
    let mut budget = Budget::default_budget();
    assert!(
        clean_ck0::infer(&env, &t(&env, &good), &mut budget).is_ok(),
        "let x : Nat := 3; 0 types"
    );
    // Negative control: the value `Eq.refl 3 : 3 = 3` is not a `Nat`.
    let bad = RawExpr::Let(
        Box::new(r_const("Nat")),
        Box::new(refl_nat(lit(3))),
        Box::new(lit(0)),
    );
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::infer(&env, &t(&env, &bad), &mut budget),
        Err(clean_ck0::InferError::TypeMismatch),
        "let x : Nat := Eq.refl 3; 0 must be refused"
    );
}

/// Under binders `A : Prop, h1 h2 : A, P : A → Prop, f : P h2 → Nat, p : P h1`,
/// `f p` types only by proof irrelevance (`h1 ≡ h2`), decided in the context.
#[test]
fn an_argument_under_binders_is_compared_in_its_context() {
    let env = env();
    let prop = r_prop();
    // Context, outermost first: A=#5, h1=#4, h2=#3, P=#2, f=#1, p=#0 at the body.
    let ty = r_pi(
        prop.clone(),
        r_pi(
            r_bvar(0),
            r_pi(
                r_bvar(1),
                r_pi(
                    r_pi(r_bvar(2), prop.clone()),
                    r_pi(
                        r_pi(r_app(r_bvar(0), r_bvar(1)), r_const("Nat")),
                        r_pi(r_app(r_bvar(1), r_bvar(3)), r_const("Nat")),
                    ),
                ),
            ),
        ),
    );
    let lam = |dom: RawExpr, body: RawExpr| r_lam(dom, body);
    let proof = lam(
        prop.clone(),
        lam(
            r_bvar(0),
            lam(
                r_bvar(1),
                lam(
                    r_pi(r_bvar(2), prop),
                    lam(
                        r_pi(r_app(r_bvar(0), r_bvar(1)), r_const("Nat")),
                        lam(r_app(r_bvar(1), r_bvar(3)), r_app(r_bvar(1), r_bvar(0))),
                    ),
                ),
            ),
        ),
    );
    assert!(
        checks(&env, &ty, &proof),
        "f p : Nat by proof irrelevance under binders"
    );
    // Negative control: with `A : Type`, `h1` and `h2` are not proofs, `P h1`
    // is not `P h2`, and `f p` does not type.
    let swap_sort = |e: &RawExpr| match e {
        RawExpr::Pi(bi, _, body) => RawExpr::Pi(*bi, Box::new(r_sort(1)), body.clone()),
        RawExpr::Lam(bi, _, body) => RawExpr::Lam(*bi, Box::new(r_sort(1)), body.clone()),
        other => panic!("binder expected, got {other:?}"),
    };
    let (ty_t, proof_t) = (swap_sort(&ty), swap_sort(&proof));
    // `P : A → Prop` is still a type, so the statement itself is well formed.
    let mut budget = Budget::default_budget();
    assert!(
        clean_ck0::infer_sort(&env, &t(&env, &ty_t), &mut budget).is_ok(),
        "the statement over A : Type is a type"
    );
    assert!(
        !checks(&env, &ty_t, &proof_t),
        "control: over A : Type, f p does not type (no proof irrelevance)"
    );
}
