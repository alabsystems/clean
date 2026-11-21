// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-founded steps inlined with their IH a direct call (X4 R1.4), and the
//! commuting conversion of an over-applied case analysis (R1.6).

use super::{expr_to_code, LcnfContext};
use crate::lcnf::{Alt, Arg, Code, FunDecl, LetValue};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, Name};

fn app(head: Expr, args: Vec<Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn arrow(dom: Expr, cod: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, cod)
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn cst_u1(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())])
}

/// The first local function named `name` on `code`'s spine.
fn find_fun<'a>(code: &'a Code, name: &str) -> &'a FunDecl {
    match code {
        Code::Fun(decl, _) if decl.name.to_string() == name => decl,
        Code::Fun(_, rest) | Code::Let(_, rest) | Code::JoinPoint(_, rest) => find_fun(rest, name),
        other => panic!("no local function `{name}` in {other:?}"),
    }
}

fn find_go(code: &Code) -> &FunDecl {
    find_fun(code, "_rec")
}

/// The variable `code` returns, through `x := y` aliases, on its LAST path,
/// with every call of `go` on the way.
fn tail_of(code: &Code, go: FVarId) -> (Vec<(FVarId, Vec<Arg>)>, FVarId) {
    let mut calls = Vec::new();
    let mut alias = std::collections::HashMap::new();
    let mut cur = code;
    loop {
        match cur {
            Code::Let(decl, rest) => {
                if let LetValue::FVar { fvar, args } = &decl.value {
                    if *fvar == go {
                        calls.push((decl.fvar_id, args.clone()));
                    } else if args.is_empty() {
                        alias.insert(decl.fvar_id, *fvar);
                    }
                }
                cur = rest;
            }
            Code::Fun(_, rest) | Code::JoinPoint(_, rest) => cur = rest,
            Code::Cases(cases) => {
                cur = match cases.alts.last() {
                    Some(Alt::Ctor { body, .. } | Alt::Default(body)) => body,
                    None => panic!("empty cases"),
                };
            }
            Code::Return(r) => {
                let mut r = *r;
                while let Some(next) = alias.get(&r) {
                    r = *next;
                }
                return (calls, r);
            }
            other => panic!("unexpected code on the tail path: {other:?}"),
        }
    }
}

/// `sumTo x acc` by `WellFounded.fixF` with the step
/// `fun x ih acc => Nat.casesOn x acc (fun k => ih k True.intro (acc + 1))`.
fn wf_sum(step_uses_ih_unapplied: bool) -> Expr {
    let ih_ty = arrow(nat(), arrow(Expr::const_str("True"), arrow(nat(), nat())));
    // Under `x ih acc k`: k = 0, acc = 1, ih = 2, x = 3.
    let recur = if step_uses_ih_unapplied {
        app(
            Expr::const_str("apply3"),
            vec![Expr::bvar(2), Expr::bvar(0)],
        )
    } else {
        app(
            Expr::bvar(2),
            vec![
                Expr::bvar(0),
                Expr::const_str("True.intro"),
                app(
                    Expr::const_str("Nat.add"),
                    vec![Expr::bvar(1), Expr::nat_lit(1)],
                ),
            ],
        )
    };
    let cases = app(
        cst_u1("Nat.casesOn"),
        vec![
            lam(nat(), nat()),
            Expr::bvar(2),
            Expr::bvar(0),
            lam(nat(), recur),
        ],
    );
    let step = lam(nat(), lam(ih_ty, lam(nat(), cases)));
    app(
        cst_u1("WellFounded.fixF"),
        vec![
            nat(),
            lam(nat(), lam(nat(), Expr::const_str("True"))),
            lam(nat(), arrow(nat(), nat())),
            step,
            Expr::const_str("n"),
            Expr::const_str("True.intro"),
            Expr::nat_lit(7),
        ],
    )
}

#[test]
fn test_wf_fix_uncurry_drops_proof() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let code = expr_to_code(&mut ctx, &wf_sum(false)).expect("lowers");
    let go = find_fun(&code, "_wf_rec");
    assert_eq!(
        go.params.len(),
        3,
        "go takes the value, the erased proof slot and acc: {go:?}"
    );
    let (calls, ret) = tail_of(&go.body, go.fvar_id);
    assert_eq!(calls.len(), 1, "one recursive call: {:?}", go.body);
    let (call, args) = &calls[0];
    assert_eq!(args.len(), 3, "a full application (k, proof, acc + 1)");
    assert_eq!(args[1], Arg::Erased, "the decrease proof is erased");
    assert_eq!(*call, ret, "the recursive call is the step's tail");
}

#[test]
fn test_wf_unapplied_ih_keeps_the_closure_lowering() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let code = expr_to_code(&mut ctx, &wf_sum(true)).expect("lowers");
    let go = find_fun(&code, "_wf_rec");
    // The closure path: go(step, v, hr), the step a closure parameter.
    assert_eq!(go.params.len(), 3);
    let Code::Let(first, _) = go.body.as_ref() else {
        panic!("closure path binds the IH first: {:?}", go.body);
    };
    assert!(
        matches!(&first.value, LetValue::FVar { fvar, args } if *fvar == go.fvar_id && args.len() == 1),
        "ih := go step (a partial application): {first:?}"
    );
}

/// `Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
///   (fun pred ih acc => Bool.casesOn (motive := fun _ => (Nat → Nat) → Nat)
///      c (fun g => g acc) (fun g => g (acc + 1)) ih) n 7`.
fn generalising_match(extra_is_ih: bool) -> Expr {
    let fn_ty = arrow(nat(), nat());
    // Inside the cases alternative `fun g`: g = 0, acc = 1, ih = 2, pred = 3.
    let f_alt = lam(fn_ty.clone(), app(Expr::bvar(0), vec![Expr::bvar(1)]));
    let t_alt = lam(
        fn_ty.clone(),
        app(
            Expr::bvar(0),
            vec![app(
                Expr::const_str("Nat.add"),
                vec![Expr::bvar(1), Expr::nat_lit(1)],
            )],
        ),
    );
    // Under `pred ih acc`: acc = 0, ih = 1.
    let passed = if extra_is_ih {
        Expr::bvar(1)
    } else {
        Expr::const_str("someFn")
    };
    let cases = app(
        cst_u1("Bool.casesOn"),
        vec![
            lam(Expr::const_str("Bool"), arrow(fn_ty.clone(), nat())),
            Expr::const_str("c"),
            f_alt,
            t_alt,
            passed,
        ],
    );
    let succ = lam(nat(), lam(fn_ty, lam(nat(), cases)));
    app(
        Expr::const_str("Nat.rec"),
        vec![
            lam(nat(), arrow(nat(), nat())),
            lam(nat(), Expr::bvar(0)),
            succ,
            Expr::const_str("n"),
            Expr::nat_lit(7),
        ],
    )
}

fn succ_arm(go: &FunDecl) -> &Code {
    let Code::Cases(cases) = go.body.as_ref() else {
        panic!("go's body is a Cases: {:?}", go.body);
    };
    match &cases.alts[1] {
        Alt::Default(body) => body,
        other => panic!("successor arm expected: {other:?}"),
    }
}

#[test]
fn test_rec_over_applied_cases_pushed_into_arms() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let code = expr_to_code(&mut ctx, &generalising_match(true)).expect("lowers");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 2, "go takes the scrutinee and acc");
    let (calls, ret) = tail_of(succ_arm(go), go.fvar_id);
    assert_eq!(
        calls.len(),
        1,
        "the IH became a call inside the alternative"
    );
    assert_eq!(calls[0].1.len(), 2, "a full application (pred, acc + 1)");
    assert_eq!(calls[0].0, ret, "and it is the alternative's tail");
}

#[test]
fn test_rec_over_applied_cases_without_an_ih_is_untouched() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let code = expr_to_code(&mut ctx, &generalising_match(false)).expect("lowers");
    let go = find_go(&code);
    // No IH is passed, so the conversion does not fire and no recursive call
    // exists at all.
    let (calls, _) = tail_of(succ_arm(go), go.fvar_id);
    assert!(calls.is_empty(), "{:?}", go.body);
}
