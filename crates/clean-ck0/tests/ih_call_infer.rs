// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A derived ι-rule's IH call, `Const(I.rec)`, is typed by its recursor type
//! (`docs/DECISIONS.md` R147, the note on the merge with R162).
//!
//! R147's `infer_proj` takes the sort of the whnf'd structure type (Lean's
//! `is_prop`). When that type is a recursor's reduct, it holds the IH call the
//! ι-rule built, `Const(Nat.rec)`, a form only derived rules produce. `infer`
//! had no rule for it, so the projection failed with `UnknownConst`: the shape
//! of the `Nat.below` encoding behind structural recursion (`Nat.beq._f` in
//! `crates/clean-olean/tests/vf4_chk_lia_quorum.rs`). The control: untrusted
//! input still cannot name a recursor as a constant.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, Budget, Constructor, InductiveDecl, InferError, MinimalEnv, Name, RawExpr,
    RawLevel, Term,
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

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &MinimalEnv, raw: &RawExpr) -> Term {
    Term::validate(env, raw, 0, 0).expect("term validates")
}

/// `Nat : Type` with `zero : Nat`, `succ : Nat → Nat`.
fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1)),
        constructors: vec![
            Constructor {
                name: n("Nat.zero"),
                type_: vlvl(&b, &r_const("Nat")),
            },
            Constructor {
                name: n("Nat.succ"),
                type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat"))),
            },
        ],
    }
}

/// `structure Pair (A B : Type) : Type where mk :: (a : A) (b : B)`.
fn pair_decl() -> InductiveDecl {
    let b = boot(&[("Pair", 0), ("Pair.mk", 0)]);
    let ty = r_pi(r_sort(1), r_pi(r_sort(1), r_sort(1)));
    // (A B : Type) → (a : A) → (b : B) → Pair A B
    let mk_ty = r_pi(
        r_sort(1),
        r_pi(
            r_sort(1),
            r_pi(
                r_bvar(1),
                r_pi(
                    r_bvar(1),
                    r_apps(r_const("Pair"), vec![r_bvar(3), r_bvar(2)]),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("Pair"),
        num_level_params: 0,
        num_params: 2,
        type_: vlvl(&b, &ty),
        constructors: vec![Constructor {
            name: n("Pair.mk"),
            type_: vlvl(&b, &mk_ty),
        }],
    }
}

fn env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, pair_decl()).expect("Pair admits");
    env
}

fn infer(env: &MinimalEnv, raw: &RawExpr) -> Result<Term, InferError> {
    let term = Term::validate(env, raw, 0, 0).expect("term validates");
    let mut budget = Budget::default_budget();
    clean_ck0::infer(env, &term, &mut budget)
}

/// `fun (n : Nat) (x : Nat.rec (motive := fun _ => Type) Nat (fun _ ih => Pair Nat ih) (succ n)) => x.0`.
/// `x`'s type reduces by ι to `Pair Nat (Nat.rec … n)`, whose second argument
/// is the IH call the rule built.
#[test]
fn test_ih_call_projection_out_of_a_recursor_reduct_infers() {
    let env = env();
    let motive = r_lam(r_const("Nat"), r_sort(1));
    let succ_minor = r_lam(
        r_const("Nat"),
        r_lam(
            r_sort(1),
            r_apps(r_const("Pair"), vec![r_const("Nat"), r_bvar(0)]),
        ),
    );
    let x_ty = r_apps(
        RawExpr::Elim(n("Nat"), level(2), vec![]),
        vec![
            motive,
            r_const("Nat"),
            succ_minor,
            r_app(r_const("Nat.succ"), r_bvar(0)),
        ],
    );
    let term = r_lam(
        r_const("Nat"),
        r_lam(x_ty, RawExpr::Proj(n("Pair"), 0, Box::new(r_bvar(0)))),
    );
    let ty = infer(&env, &term).expect("x.0 types: Pair Nat (Nat.rec … n) is not a proposition");
    let expected = vlvl(
        &env,
        &r_pi(
            r_const("Nat"),
            r_pi(
                r_apps(
                    RawExpr::Elim(n("Nat"), level(2), vec![]),
                    vec![
                        r_lam(r_const("Nat"), r_sort(1)),
                        r_const("Nat"),
                        r_lam(
                            r_const("Nat"),
                            r_lam(
                                r_sort(1),
                                r_apps(r_const("Pair"), vec![r_const("Nat"), r_bvar(0)]),
                            ),
                        ),
                        r_app(r_const("Nat.succ"), r_bvar(0)),
                    ],
                ),
                r_const("Nat"),
            ),
        ),
    );
    let mut budget = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &ty, &expected, &mut budget).expect("within budget"),
        "x.0 : Nat, got {ty:?}"
    );
}

/// The control: a recursor named as a constant is refused at the boundary, so
/// the IH-call form reaches `infer` only from a derived rule.
#[test]
fn test_ih_call_control_untrusted_recursor_constant_is_refused() {
    let env = env();
    let raw = RawExpr::Const(n("Nat.rec"), vec![level(1)]);
    Term::validate(&env, &raw, 0, 0).expect_err("a recursor in Const position is refused");
}
