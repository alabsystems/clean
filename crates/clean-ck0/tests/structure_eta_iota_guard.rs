// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Structure η at a recursor's major premise, ported from Lean's
//! `to_cnstr_when_structure` (`src/kernel/inductive.h`, v4.30.0-rc2 and
//! v4.33.1; decision R147).
//!
//! When the major is not a constructor application, Lean infers its type,
//! requires that type to be headed by the recursor's structure, and leaves
//! the major as it is when that type is a proposition (v4.33.1 asks
//! `is_prop`, leanprover/lean4#14843). Only then does it expand the major to
//! `S.mk m.1 … m.n`. Before the port ck0 expanded every non-constructor major
//! of a structure without looking at its type, so it equated a stuck
//! `And.rec` with its minor's value, which both pinned Lean tags refuse, and
//! it left a constant major stuck, which Lean expands.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, infer, is_def_eq, Budget, Constructor, Env, InductiveDecl, MinimalEnv, Name,
    RawExpr, RawLevel, Term,
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
fn r_proj(struct_name: &str, idx: u32, e: RawExpr) -> RawExpr {
    RawExpr::Proj(n(struct_name), idx, Box::new(e))
}
/// The recursor of `ind` eliminating into `Sort 1` (it takes no level of its
/// own besides the motive's).
fn r_rec_into_type(ind: &str) -> RawExpr {
    RawExpr::Elim(n(ind), RawLevel::Succ(Box::new(RawLevel::Zero)), vec![])
}

fn v(env: &dyn Env, raw: &RawExpr) -> Term {
    Term::validate_closed(env, raw).expect("term validates")
}
fn boot(names: &[&str]) -> MinimalEnv {
    names
        .iter()
        .fold(MinimalEnv::new(), |env, name| env.with_const(n(name), 0))
}

/// `And (a b : Prop) : Prop` with `And.intro : a → b → And a b`: a Prop
/// structure with large elimination.
fn and_decl() -> InductiveDecl {
    let b = boot(&["And", "And.intro"]);
    let intro = r_pi(
        r_sort(0),
        r_pi(
            r_sort(0),
            r_pi(
                r_bvar(1),
                r_pi(
                    r_bvar(1),
                    r_apps(r_const("And"), vec![r_bvar(3), r_bvar(2)]),
                ),
            ),
        ),
    );
    InductiveDecl {
        name: n("And"),
        num_level_params: 0,
        num_params: 2,
        type_: v(&b, &r_pi(r_sort(0), r_pi(r_sort(0), r_sort(0)))),
        constructors: vec![Constructor {
            name: n("And.intro"),
            type_: v(&b, &intro),
        }],
    }
}

/// `SB : Type` with `SB.mk : Bool → SB`: the same shape outside `Prop`.
fn sb_decl() -> InductiveDecl {
    let b = boot(&["SB", "SB.mk", "Bool"]);
    InductiveDecl {
        name: n("SB"),
        num_level_params: 0,
        num_params: 0,
        type_: v(&b, &r_sort(1)),
        constructors: vec![Constructor {
            name: n("SB.mk"),
            type_: v(&b, &r_pi(r_const("Bool"), r_const("SB"))),
        }],
    }
}

fn env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    let ty = v(&env, &r_sort(1));
    env = env.with_const_typed(n("Bool"), 0, ty);
    let bool_ty = v(&env, &r_const("Bool"));
    env = env.with_const_typed(n("Bool.true"), 0, bool_ty);
    let prop = v(&env, &r_sort(0));
    env = env
        .with_const_typed(n("T"), 0, prop.clone())
        .with_const_typed(n("U"), 0, prop);
    add_inductive(&mut env, and_decl()).expect("And admitted");
    add_inductive(&mut env, sb_decl()).expect("SB admitted");
    let and_tu = v(
        &env,
        &r_apps(r_const("And"), vec![r_const("T"), r_const("U")]),
    );
    let sb = v(&env, &r_const("SB"));
    env.with_const_typed(n("hc"), 0, and_tu)
        .with_const_typed(n("xb"), 0, sb)
}

fn def_eq(env: &MinimalEnv, a: &RawExpr, b: &RawExpr) -> bool {
    is_def_eq(env, &v(env, a), &v(env, b), &mut Budget::default_budget()).expect("budget")
}

/// Both sides of every comparison below are well typed at the same type, so
/// the answer is a statement about conversion only.
fn assert_same_type(env: &MinimalEnv, a: &RawExpr, b: &RawExpr) {
    let ta = infer(env, &v(env, a), &mut Budget::default_budget()).expect("lhs is well typed");
    let tb = infer(env, &v(env, b), &mut Budget::default_budget()).expect("rhs is well typed");
    assert!(
        is_def_eq(env, &ta, &tb, &mut Budget::default_budget()).expect("budget"),
        "the two sides must have one type"
    );
}

/// `And.rec (motive := fun _ => Bool) (fun _ _ => true) h ≡ true` for a
/// variable `h : And T U`. Lean leaves the recursor stuck (its major's type
/// is a proposition), so the conversion is refused. The control is the same
/// shape over the `Type` structure `SB`, where the expansion fires.
#[test]
fn structure_eta_at_iota_leaves_a_proof_major_stuck() {
    let env = env();
    let and_tu = r_apps(r_const("And"), vec![r_const("T"), r_const("U")]);
    let and_rec = |major: RawExpr| {
        r_apps(
            r_rec_into_type("And"),
            vec![
                r_const("T"),
                r_const("U"),
                r_lam(and_tu.clone(), r_const("Bool")),
                r_lam(r_const("T"), r_lam(r_const("U"), r_const("Bool.true"))),
                major,
            ],
        )
    };
    let subject = r_lam(and_tu.clone(), and_rec(r_bvar(0)));
    let constant = r_lam(and_tu.clone(), r_const("Bool.true"));
    assert_same_type(&env, &subject, &constant);
    assert!(
        !def_eq(&env, &subject, &constant),
        "fun h => And.rec .. h must not convert to fun h => true"
    );
    // A constant proof major stays stuck too.
    assert_same_type(&env, &and_rec(r_const("hc")), &r_const("Bool.true"));
    assert!(
        !def_eq(&env, &and_rec(r_const("hc")), &r_const("Bool.true")),
        "And.rec .. hc must not convert to true"
    );

    // Control: over `SB : Type` the major is expanded and the rule fires.
    let sb_rec = r_apps(
        r_rec_into_type("SB"),
        vec![
            r_lam(r_const("SB"), r_const("Bool")),
            r_lam(r_const("Bool"), r_const("Bool.true")),
            r_bvar(0),
        ],
    );
    let control = r_lam(r_const("SB"), sb_rec);
    let control_constant = r_lam(r_const("SB"), r_const("Bool.true"));
    assert_same_type(&env, &control, &control_constant);
    assert!(
        def_eq(&env, &control, &control_constant),
        "control: fun x => SB.rec .. x converts to fun x => true"
    );
}

/// Lean expands a major that is a constant of a structure type (it is not a
/// constructor application), so `SB.rec (fun _ => Bool) (fun b => b) xb` is
/// `xb.1`. Before the port ck0 looked the constant up as a constructor, found
/// no rule and left the recursor stuck.
#[test]
fn structure_eta_at_iota_expands_a_constant_major() {
    let env = env();
    let subject = r_apps(
        r_rec_into_type("SB"),
        vec![
            r_lam(r_const("SB"), r_const("Bool")),
            r_lam(r_const("Bool"), r_bvar(0)),
            r_const("xb"),
        ],
    );
    let field = r_proj("SB", 0, r_const("xb"));
    assert_same_type(&env, &subject, &field);
    assert!(
        def_eq(&env, &subject, &field),
        "SB.rec .. xb must convert to xb.1"
    );
}
