// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! K-like reduction inside `whnf` (Lean's `to_cnstr_when_K`, which
//! `inductive_reduce_rec` applies in whnf; `docs/DECISIONS.md` R147, the note on
//! the merge with R162).
//!
//! The eliminator of a K-target on a VARIABLE major whose type is its
//! constructor's reduces even where only `whnf` runs: here, the head type of
//! an application, which must reduce to a function type. R162 applied K in
//! `def_eq` only. The round-5 merge kept R147's guard that refuses structure η
//! on a proposition, and that guard stopped the unguarded η that had reduced a
//! `True`-like K-target on main. The `Eq` major of another type stays stuck.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, BigNat, Budget, Constructor, InductiveDecl, InferError, MinimalEnv, Name,
    RawExpr, RawLevel, RawLit, Term,
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
fn level(k: u32) -> RawLevel {
    let mut l = RawLevel::Zero;
    for _ in 0..k {
        l = RawLevel::Succ(Box::new(l));
    }
    l
}
fn lit(v: u64) -> RawExpr {
    RawExpr::Lit(RawLit::Nat(BigNat::from_u64(v)))
}

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &MinimalEnv, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

/// `Nat : Type` with `zero : Nat`, `succ : Nat → Nat`.
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

/// `Eq.{u} {A : Sort u} (a : A) : A → Prop` with `refl (a) : Eq a a`
/// (num_params = 2, as `r162_lean_kernel_rules.rs` builds it).
fn eq_decl() -> InductiveDecl {
    let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
    let p0 = RawExpr::Sort(RawLevel::Param(0));
    let ty = r_pi(p0.clone(), r_pi(r_bvar(0), r_pi(r_bvar(1), r_sort(0))));
    let refl_ty = r_pi(
        p0,
        r_pi(
            r_bvar(0),
            r_apps(
                r_const_p("Eq", vec![RawLevel::Param(0)]),
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

/// `True : Prop` with `intro : True`: a K-target that is also registered as an
/// η-structure (one constructor, no indices, not recursive).
fn true_decl() -> InductiveDecl {
    let b = boot(&[("True", 0), ("True.intro", 0)]);
    InductiveDecl {
        name: n("True"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(0), 0),
        constructors: vec![Constructor {
            name: n("True.intro"),
            type_: vlvl(&b, &r_const("True"), 0),
        }],
    }
}

fn env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, eq_decl()).expect("Eq admits");
    add_inductive(&mut env, true_decl()).expect("True admits");
    env
}

fn infer(env: &MinimalEnv, raw: &RawExpr) -> Result<Term, InferError> {
    let term = Term::validate(env, raw, 0, 0).expect("term validates");
    let mut budget = Budget::default_budget();
    clean_ck0::infer(env, &term, &mut budget)
}

fn eq_nat(a: RawExpr, b: RawExpr) -> RawExpr {
    r_apps(r_const_p("Eq", vec![level(1)]), vec![r_const("Nat"), a, b])
}

/// `fun (h : Eq Nat zero y) (f : Eq.rec (motive := fun b _ => Type) (Nat → Nat) h) => f 0`.
/// `f`'s type must reduce to `Nat → Nat` for the application to type.
fn apply_through_eq_rec(y: RawExpr) -> RawExpr {
    let zero = r_const("Nat.zero");
    // Under the binder h (#0): motive : (b : Nat) → Eq Nat zero b → Sort 2.
    let motive = r_lam(
        r_const("Nat"),
        r_lam(eq_nat(zero.clone(), r_bvar(0)), r_sort(1)),
    );
    let f_ty = r_apps(
        RawExpr::Elim(n("Eq"), level(2), vec![level(1)]),
        vec![
            r_const("Nat"),
            zero.clone(),
            motive,
            r_pi(r_const("Nat"), r_const("Nat")),
            y.clone(),
            r_bvar(0),
        ],
    );
    r_lam(eq_nat(zero, y), r_lam(f_ty, r_app(r_bvar(0), lit(0))))
}

#[test]
fn test_k_like_eq_rec_on_a_variable_major_reduces_in_whnf() {
    let env = env();
    let term = apply_through_eq_rec(r_const("Nat.zero"));
    infer(&env, &term).expect("K: Eq.rec … h ≡ Nat → Nat for h : zero = zero");
}

#[test]
fn test_k_like_control_eq_rec_on_a_major_of_another_type_stays_stuck() {
    let env = env();
    let term = apply_through_eq_rec(r_app(r_const("Nat.succ"), r_const("Nat.zero")));
    assert_eq!(
        infer(&env, &term).map(|_| ()),
        Err(InferError::NotAFunction),
        "h : zero = succ zero is not Eq.refl's type, so the eliminator stays stuck"
    );
}

/// `fun (h : True) (f : True.rec (motive := fun _ => Type) (Nat → Nat) h) => f 0`:
/// R147's guard refuses structure η on a proposition, and K reduces it instead.
#[test]
fn test_k_like_true_rec_on_a_variable_major_reduces_in_whnf() {
    let env = env();
    let f_ty = r_apps(
        RawExpr::Elim(n("True"), level(2), vec![]),
        vec![
            r_lam(r_const("True"), r_sort(1)),
            r_pi(r_const("Nat"), r_const("Nat")),
            r_bvar(0),
        ],
    );
    let term = r_lam(r_const("True"), r_lam(f_ty, r_app(r_bvar(0), lit(0))));
    infer(&env, &term).expect("K: True.rec … h ≡ Nat → Nat for h : True");
}
