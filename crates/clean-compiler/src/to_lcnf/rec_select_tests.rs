// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One `go` for a lifted mutual block (X4 R1.3), on hand-built kernel terms
//! of `mutual_lift`'s shape.

use super::{expr_to_code, LcnfContext};
use crate::lcnf::{Alt, Arg, Code, FunDecl, LetValue};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};

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

fn one() -> Level {
    Level::succ(Level::zero())
}

fn pprod(a: Expr, b: Expr) -> Expr {
    app(
        Expr::const_(Name::from_string("PProd"), vec![one(), one()]),
        vec![a, b],
    )
}

fn pprod_mk(a_ty: Expr, b_ty: Expr, a: Expr, b: Expr) -> Expr {
    app(
        Expr::const_(Name::from_string("PProd.mk"), vec![one(), one()]),
        vec![a_ty, b_ty, a, b],
    )
}

fn proj(idx: u32, e: Expr) -> Expr {
    Expr::proj(Name::from_string("PProd"), idx, e)
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    app(Expr::const_str("Nat.add"), vec![a, b])
}

/// `(Nat.rec motive zero succ n).(entry) extras…` with
/// `motive := fun _ => PProd A B`.
fn entry(a: Expr, b: Expr, zero: Expr, succ: Expr, entry: u32, extras: Vec<Expr>) -> Expr {
    let motive = lam(nat(), pprod(a, b));
    let rec = app(
        Expr::const_str("Nat.rec"),
        vec![motive, zero, succ, Expr::const_str("n")],
    );
    app(proj(entry, rec), extras)
}

/// `even`/`odd`-shaped: member 0 calls member 1 and member 1 calls member 0,
/// both in tail position. `succ := fun pred ih => ⟨fun a => ih.2 a, fun a =>
/// ih.1 (a + 1)⟩`.
fn ping_pong() -> Expr {
    let t = arrow(nat(), nat());
    let zero = pprod_mk(
        t.clone(),
        t.clone(),
        lam(nat(), Expr::bvar(0)),
        lam(nat(), Expr::bvar(0)),
    );
    // Under `pred ih a`: ih = BVar 1.
    let member0 = lam(nat(), Expr::app(proj(1, Expr::bvar(1)), Expr::bvar(0)));
    let member1 = lam(
        nat(),
        Expr::app(
            proj(0, Expr::bvar(1)),
            nat_add(Expr::bvar(0), Expr::nat_lit(1)),
        ),
    );
    let succ = lam(
        nat(),
        lam(
            pprod(t.clone(), t.clone()),
            pprod_mk(t.clone(), t.clone(), member0, member1),
        ),
    );
    entry(t.clone(), t, zero, succ, 0, vec![Expr::nat_lit(7)])
}

fn find_go(code: &Code) -> &FunDecl {
    match code {
        Code::Fun(decl, _) => decl,
        Code::Let(_, rest) | Code::JoinPoint(_, rest) => find_go(rest),
        other => panic!("no synthesized go in {other:?}"),
    }
}

/// Every `go` call anywhere in `code`, with its arguments.
fn go_calls(code: &Code, go: clean_kernel::FVarId, out: &mut Vec<Vec<Arg>>) {
    match code {
        Code::Let(decl, rest) => {
            if let LetValue::FVar { fvar, args } = &decl.value {
                if *fvar == go {
                    out.push(args.clone());
                }
            }
            go_calls(rest, go, out);
        }
        Code::Fun(decl, rest) | Code::JoinPoint(decl, rest) => {
            go_calls(&decl.body, go, out);
            go_calls(rest, go, out);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                let (Alt::Ctor { body, .. } | Alt::Default(body)) = alt;
                go_calls(body, go, out);
            }
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

/// Whether `code` builds a `PProd` anywhere.
fn builds_tuple(code: &Code) -> bool {
    let text = format!("{code:?}");
    text.contains("PProd.mk") || text.contains("\"mk\"")
}

#[test]
fn test_rec_pprod_selector_family() {
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let code = expr_to_code(&mut ctx, &ping_pong()).expect("lowers");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 3, "go(sel, scrut, a)");
    assert!(!builds_tuple(&code), "no tuple is built: {code:?}");
    let mut calls = Vec::new();
    go_calls(&go.body, go.fvar_id, &mut calls);
    assert_eq!(calls.len(), 2, "each member calls the other through go");
    assert!(calls.iter().all(|args| args.len() == 3), "{calls:?}");
    let mut entry_calls = Vec::new();
    go_calls(&code, go.fvar_id, &mut entry_calls);
    assert_eq!(entry_calls.len(), 3, "the entry is a call of go too");
}

#[test]
fn test_rec_pprod_whole_ih_use_falls_back() {
    // `Nat.brecOn`'s shape uses the IH whole (as `below`); here member 0
    // passes it whole to a function. No selector applies, and the k = 0
    // lowering does.
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let t = arrow(nat(), nat());
    let zero = pprod_mk(
        t.clone(),
        t.clone(),
        lam(nat(), Expr::bvar(0)),
        lam(nat(), Expr::bvar(0)),
    );
    // Under `pred ih a`: ih = BVar 1.
    let member0 = lam(
        nat(),
        app(
            Expr::const_str("Nat.mul"),
            vec![Expr::bvar(1), Expr::bvar(0)],
        ),
    );
    let member1 = lam(nat(), Expr::app(proj(0, Expr::bvar(1)), Expr::bvar(0)));
    let succ = lam(
        nat(),
        lam(
            pprod(t.clone(), t.clone()),
            pprod_mk(t.clone(), t.clone(), member0, member1),
        ),
    );
    let expr = entry(t.clone(), t, zero, succ, 1, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("lowers as before");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 1, "no selector, no slots: {:?}", go.params);
}

#[test]
fn test_rec_pprod_heterogeneous_arity_pads_with_erased() {
    // Member 0 takes two arguments, member 1 one: K = 2, and member 1's
    // calls pass an erased pad in the second slot.
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let t0 = arrow(nat(), arrow(nat(), nat()));
    let t1 = arrow(nat(), nat());
    let zero = pprod_mk(
        t0.clone(),
        t1.clone(),
        lam(nat(), lam(nat(), Expr::bvar(0))),
        lam(nat(), Expr::bvar(0)),
    );
    // Under `pred ih a b`: member 0 calls member 1 with `a`.
    let member0 = lam(
        nat(),
        lam(nat(), Expr::app(proj(1, Expr::bvar(2)), Expr::bvar(1))),
    );
    // Under `pred ih a`: member 1 calls member 0 with `a a`.
    let member1 = lam(
        nat(),
        app(proj(0, Expr::bvar(1)), vec![Expr::bvar(0), Expr::bvar(0)]),
    );
    let succ = lam(
        nat(),
        lam(
            pprod(t0.clone(), t1.clone()),
            pprod_mk(t0.clone(), t1.clone(), member0, member1),
        ),
    );
    let expr = entry(t0, t1, zero, succ, 1, vec![Expr::nat_lit(7)]);
    let code = expr_to_code(&mut ctx, &expr).expect("lowers");
    let go = find_go(&code);
    assert_eq!(go.params.len(), 4, "go(sel, scrut, s1, s2)");
    let mut calls = Vec::new();
    go_calls(&code, go.fvar_id, &mut calls);
    assert!(
        calls.iter().all(|args| args.len() == 4),
        "every call fills every slot: {calls:?}"
    );
    let padded = calls.iter().filter(|args| args[3] == Arg::Erased).count();
    assert_eq!(
        padded, 2,
        "member 1's call and the entry are padded: {calls:?}"
    );
}

#[test]
fn test_rec_pprod_short_call_to_a_padded_member_falls_back() {
    // Member 1 (k = 1 < K = 2) used as a value: a partial application of go
    // would await its pad, so the block keeps the k = 0 lowering.
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);
    let t0 = arrow(nat(), arrow(nat(), nat()));
    let t1 = arrow(nat(), nat());
    let zero = pprod_mk(
        t0.clone(),
        t1.clone(),
        lam(nat(), lam(nat(), Expr::bvar(0))),
        lam(nat(), Expr::bvar(0)),
    );
    let member0 = lam(
        nat(),
        lam(
            nat(),
            app(
                Expr::const_str("Nat.mul"),
                vec![proj(1, Expr::bvar(2)), Expr::bvar(1)],
            ),
        ),
    );
    let member1 = lam(nat(), Expr::bvar(0));
    let succ = lam(
        nat(),
        lam(
            pprod(t0.clone(), t1.clone()),
            pprod_mk(t0.clone(), t1.clone(), member0, member1),
        ),
    );
    let expr = entry(
        t0,
        t1,
        zero,
        succ,
        0,
        vec![Expr::nat_lit(7), Expr::nat_lit(8)],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("lowers as before");
    assert_eq!(find_go(&code).params.len(), 1);
}
