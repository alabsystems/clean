// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IH placeholders and `go`'s uncurried telescope (X4 R1.1 and R1.2).

use super::rec_ih::{go_telescope, peel_lams, syntactic_action, syntactic_arity};
use super::{expr_to_code, LcnfContext};
use crate::lcnf::{Alt, Arg, Code, FunDecl, LetValue};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId};

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

fn io(ty: Expr) -> Expr {
    Expr::app(Expr::const_str("IO"), ty)
}

fn mdata(e: Expr) -> Expr {
    Expr::mdata(Vec::new(), e)
}

#[test]
fn test_syntactic_arity_counts_lambdas_through_metadata_only() {
    let body = Expr::bvar(0);
    let two = lam(nat(), mdata(lam(nat(), body.clone())));
    assert_eq!(syntactic_arity(&two), 2);
    assert_eq!(syntactic_arity(&mdata(two.clone())), 2);
    // A `let` hides the binder after it: Lean's compiler would not see it.
    let behind_let = lam(
        nat(),
        Expr::let_named(
            clean_kernel::Name::anon(),
            nat(),
            Expr::nat_lit(1),
            lam(nat(), body),
            false,
        ),
    );
    assert_eq!(syntactic_arity(&behind_let), 1);
    assert_eq!(peel_lams(&two, 2), Some(Expr::bvar(0)));
    assert_eq!(peel_lams(&two, 3), None);
}

#[test]
fn test_syntactic_action_reads_io_and_unit_thunks() {
    assert!(syntactic_action(&io(nat())));
    assert!(syntactic_action(&arrow(Expr::const_str("Unit"), io(nat()))));
    assert!(syntactic_action(&mdata(io(nat()))));
    assert!(!syntactic_action(&nat()));
    assert!(!syntactic_action(&arrow(nat(), io(nat()))));
    assert!(!syntactic_action(&Expr::const_str("_")));
}

#[test]
fn test_go_telescope_is_capped_by_the_motive_and_by_want() {
    let env = Environment::with_prelude();
    // motive := fun _ => Nat → Nat → Nat
    let motive = lam(nat(), arrow(nat(), arrow(nat(), nat())));
    let full = go_telescope(&env, &motive, 2);
    assert_eq!(full.k, 2);
    assert_eq!(full.call_ty, nat());
    assert!(!full.action);
    let one = go_telescope(&env, &motive, 1);
    assert_eq!(one.k, 1);
    assert_eq!(one.call_ty, arrow(nat(), nat()));
    assert_eq!(go_telescope(&env, &motive, 9).k, 2, "the motive caps k");
    // A beta-redex motive body is read after reduction.
    let redex = lam(
        nat(),
        Expr::app(lam(Expr::type_(), arrow(nat(), io(nat()))), nat()),
    );
    let tele = go_telescope(&env, &redex, 1);
    assert_eq!(tele.k, 1);
    assert!(tele.action, "IO Nat after one argument is an action");
    // A constant motive (no binder to read) takes nothing.
    assert_eq!(go_telescope(&env, &Expr::const_str("motive"), 3).k, 0);
}

/// The `go` the lowered value synthesizes.
fn find_go(code: &Code) -> &FunDecl {
    match code {
        Code::Fun(decl, _) => decl,
        Code::Let(_, rest) | Code::JoinPoint(_, rest) => find_go(rest),
        other => panic!("no synthesized go in {other:?}"),
    }
}

/// The successor arm of a `Nat.rec` `go`.
fn succ_arm(go: &FunDecl) -> &Code {
    let Code::Cases(cases) = go.body.as_ref() else {
        panic!("go's body is a Cases: {:?}", go.body);
    };
    match &cases.alts[1] {
        Alt::Default(body) => body,
        other => panic!("successor arm expected: {other:?}"),
    }
}

/// Every call of `go` in a straight-line arm, and the arm's returned var
/// through aliases (`x := y`, which `to_ir` substitutes away).
fn calls_and_return(arm: &Code, go: FVarId) -> (Vec<(FVarId, Vec<Arg>)>, FVarId) {
    let mut calls = Vec::new();
    let mut alias = std::collections::HashMap::new();
    let mut cur = arm;
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
            Code::Return(r) => {
                let mut r = *r;
                while let Some(next) = alias.get(&r) {
                    r = *next;
                }
                return (calls, r);
            }
            other => panic!("straight-line arm expected: {other:?}"),
        }
    }
}

/// `Nat.rec (motive := fun _ => Nat → Nat) zero succ n acc0`.
fn counter(zero: Expr, succ_body: Expr, extras: Vec<Expr>) -> Expr {
    let motive = lam(nat(), arrow(nat(), nat()));
    let succ = lam(nat(), lam(arrow(nat(), nat()), succ_body));
    let mut args = vec![motive, zero, succ, Expr::const_str("n")];
    args.extend(extras);
    app(Expr::const_str("Nat.rec"), args)
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    app(Expr::const_str("Nat.add"), vec![a, b])
}

#[test]
fn test_rec_ih_head_loop_step_is_a_full_direct_call_in_tail_position() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // succ := fun pred ih acc => ih (acc + 1)
    let step = lam(
        nat(),
        Expr::app(Expr::bvar(1), nat_add(Expr::bvar(0), Expr::nat_lit(1))),
    );
    let expr = counter(lam(nat(), Expr::bvar(0)), step, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 2, "go takes the scrutinee and acc");
    let (calls, ret) = calls_and_return(succ_arm(go), go.fvar_id);
    assert_eq!(calls.len(), 1, "one recursive call");
    assert_eq!(calls[0].1.len(), 2, "a full application: (pred, acc + 1)");
    assert_eq!(calls[0].0, ret, "the recursive call is the arm's result");
}

#[test]
fn test_rec_ih_pure_ih_used_twice_is_one_call() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // succ := fun pred ih acc => Nat.add (ih acc) (ih acc)
    let step = lam(
        nat(),
        nat_add(
            Expr::app(Expr::bvar(1), Expr::bvar(0)),
            Expr::app(Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let expr = counter(lam(nat(), Expr::bvar(0)), step, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    let (calls, _) = calls_and_return(succ_arm(go), go.fvar_id);
    assert_eq!(calls.len(), 1, "the same pure application is bound once");
}

#[test]
fn test_rec_ih_action_ih_runs_at_each_occurrence() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // motive := fun _ => Nat → IO Nat;
    // succ := fun pred ih acc => Nat.mul (ih acc) (ih acc)
    let motive = lam(nat(), arrow(nat(), io(nat())));
    let pair = app(
        Expr::const_str("Nat.mul"),
        vec![
            Expr::app(Expr::bvar(1), Expr::bvar(0)),
            Expr::app(Expr::bvar(1), Expr::bvar(0)),
        ],
    );
    let succ = lam(nat(), lam(arrow(nat(), io(nat())), lam(nat(), pair)));
    let zero = lam(nat(), app(Expr::const_str("pure"), vec![Expr::bvar(0)]));
    let expr = app(
        Expr::const_str("Nat.rec"),
        vec![motive, zero, succ, Expr::const_str("n"), Expr::nat_lit(7)],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    let (calls, _) = calls_and_return(succ_arm(go), go.fvar_id);
    assert_eq!(calls.len(), 2, "an action runs at every occurrence");
}

#[test]
fn test_rec_ih_under_application_is_a_partial_application() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // succ := fun pred ih acc => Nat.mul ih acc   (ih used as a value)
    let step = lam(
        nat(),
        app(
            Expr::const_str("Nat.mul"),
            vec![Expr::bvar(1), Expr::bvar(0)],
        ),
    );
    let expr = counter(lam(nat(), Expr::bvar(0)), step, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    let (calls, _) = calls_and_return(succ_arm(go), go.fvar_id);
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].1.len(), 1, "go(pred): one argument short");
}

#[test]
fn test_rec_ih_over_application_applies_the_rest_to_the_call() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // motive := fun _ => Nat → (Nat → Nat); every minor takes ONE argument,
    // so k = 1 and `ih acc acc` applies the call's closure to the second.
    let motive = lam(nat(), arrow(nat(), arrow(nat(), nat())));
    let zero = lam(nat(), lam(nat(), Expr::bvar(0)));
    let step = lam(
        nat(),
        app(Expr::bvar(1), vec![Expr::bvar(0), Expr::bvar(0)]),
    );
    let succ = lam(nat(), lam(arrow(nat(), arrow(nat(), nat())), step));
    let expr = app(
        Expr::const_str("Nat.rec"),
        vec![motive, zero, succ, Expr::const_str("n"), Expr::nat_lit(7)],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 2, "k = 1: the scrutinee and one argument");
    let arm = succ_arm(go);
    let (calls, ret) = calls_and_return(arm, go.fvar_id);
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].1.len(), 2);
    let mut cur = arm;
    let mut applied = false;
    while let Code::Let(decl, rest) = cur {
        if let LetValue::FVar { fvar, args } = &decl.value {
            if *fvar == calls[0].0 && args.len() == 1 && decl.fvar_id == ret {
                applied = true;
            }
        }
        cur = rest;
    }
    // `ret` is the closure application itself, reached through its alias.
    assert!(
        applied,
        "the remaining argument is applied to the call: {arm:?}"
    );
}

#[test]
fn test_rec_ih_minor_with_too_few_binders_is_an_error_not_an_eta_expansion() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // zero takes acc, succ does not: want = 0, so k = 0 and both stay valid.
    let step = Expr::bvar(0);
    let expr = counter(lam(nat(), Expr::bvar(0)), step, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("k = 0 lowers as before");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 1, "no binder is invented");
}

/// `List.rec (motive := fun _ => Nat → Nat) nil cons l acc0` over `List Nat`:
/// a recursor the general arm lowering takes (not `Nat.rec`'s).
fn list_fold(nil: Expr, cons_body: Expr, extras: Vec<Expr>) -> Expr {
    let list_nat = Expr::app(Expr::const_str("List"), nat());
    let motive = lam(list_nat.clone(), arrow(nat(), nat()));
    // cons := fun head tail ih => cons_body
    let cons = lam(nat(), lam(list_nat, lam(arrow(nat(), nat()), cons_body)));
    let mut args = vec![nat(), motive, nil, cons, Expr::const_str("l")];
    args.extend(extras);
    app(Expr::const_str("List.rec"), args)
}

/// The arm of a general recursor's `go` for the constructor `ctor`.
fn ctor_arm<'a>(go: &'a FunDecl, ctor: &str) -> &'a Code {
    let Code::Cases(cases) = go.body.as_ref() else {
        panic!("go's body is a Cases: {:?}", go.body);
    };
    cases
        .alts
        .iter()
        .find_map(|alt| match alt {
            Alt::Ctor {
                ctor_name, body, ..
            } if ctor_name.to_string() == ctor => Some(body.as_ref()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no {ctor} arm in {:?}", cases.alts))
}

#[test]
fn test_rec_ih_general_recursor_tail_ih_is_a_full_direct_call_in_tail_position() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    // cons := fun head tail ih acc => ih (acc + head)
    let step = lam(
        nat(),
        Expr::app(Expr::bvar(1), nat_add(Expr::bvar(0), Expr::bvar(3))),
    );
    let expr = list_fold(lam(nat(), Expr::bvar(0)), step, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 2, "go takes the scrutinee and acc");
    let (calls, ret) = calls_and_return(ctor_arm(go, "List.cons"), go.fvar_id);
    assert_eq!(calls.len(), 1, "one recursive call");
    assert_eq!(
        calls[0].1.len(),
        2,
        "a full application: (tail, acc + head)"
    );
    assert_eq!(calls[0].0, ret, "the recursive call is the arm's result");
}
