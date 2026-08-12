// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for bridge-lemma synthesis (`inductive_local_lift_bridge.rs`,
//! rung P3 of `designs/2026-07-29-rocq-features-into-clean.md` §B).
//!
//! Every acceptance test drives the REAL checked pipeline: lift →
//! `add_inductive` → round-trip guard → synthesize → `add_decl` each bridge
//! theorem — the kernel is the referee for every generated proof term.
//! Bare environments must call `init_iff()` (and register `Bool`-free
//! fixtures) themselves.

use super::inductive_local_lift_bridge::BridgeOutcome;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

fn prop() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::zero()))
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::new())
}

/// `inductive B : Type | b : B`
fn add_base(env: &mut Environment) {
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("B"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("B.b"),
                type_: cnst("B"),
            }],
        }],
    })
    .expect("base type B must register");
}

/// `inductive Wrap (P : B → Prop) : Prop | mk : P B.b → Wrap P`
fn add_wrap(env: &mut Environment) {
    let p_ty = Expr::pi(BinderInfo::Default, cnst("B"), prop());
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        p_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::bvar(0), cnst("B.b")),
            Expr::app(cnst("Wrap"), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("Wrap"),
            type_: Expr::pi(BinderInfo::Default, p_ty, prop()),
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("container Wrap must register");
}

/// `inductive Bad : B → Prop | step : (n : B) → Wrap (fun (m : B) => Bad n) → Bad n`
fn bad_decl() -> InductiveDecl {
    let bad = |arg: Expr| Expr::app(cnst("Bad"), arg);
    let capturing_arg = Expr::lam(BinderInfo::Default, cnst("B"), bad(Expr::bvar(1)));
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("Wrap"), capturing_arg),
            bad(Expr::bvar(1)),
        ),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bad"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("Bad.step"),
                type_: step_ty,
            }],
        }],
    }
}

/// Full pipeline on a decl: lift, register, guard, synthesize, register
/// every bridge through checked `add_decl`. Returns the bridge count.
fn lift_and_bridge(env: &mut Environment, decl: &InductiveDecl) -> usize {
    let lift = env.lift_nested_locals(decl).expect("lift succeeds");
    env.add_inductive(lift.decl.clone())
        .expect("lifted block registers");
    env.verify_local_lift_anchor(decl, &lift.families)
        .expect("round-trip guard green");
    let outcome = env
        .synthesize_local_lift_bridges(decl, &lift.families)
        .expect("synthesis must not hit an invariant failure");
    let decls = match outcome {
        BridgeOutcome::Bridges(d) => d,
        BridgeOutcome::OutOfScope { reason } => {
            panic!("fixture unexpectedly out of scope: {reason}")
        }
    };
    let n = decls.len();
    for d in decls {
        let name = match &d {
            Declaration::Theorem { name, .. } => name.clone(),
            other => panic!("bridge must be a Theorem, got {other:?}"),
        };
        env.add_decl(d)
            .unwrap_or_else(|e| panic!("bridge {name} must kernel-check: {e}"));
    }
    n
}

#[test]
fn test_bridge_width_one_wrap_lands_and_kernel_checks() {
    let mut env = Environment::new();
    env.init_iff().expect("Iff registers");
    add_base(&mut env);
    add_wrap(&mut env);
    let n = lift_and_bridge(&mut env, &bad_decl());
    assert_eq!(n, 3, "mp + mpr + iff for the single family");
    for suffix in ["bridge_mp", "bridge_mpr", "bridge"] {
        let name = Name::from_string(&format!("_lifted.Wrap_1.{suffix}"));
        let info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{name} must be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} is a theorem");
    }
    // Vocabulary pin: the iff statement's RHS side mentions the ORIGINAL
    // container and no lifted family beyond the LHS.
    let iff = env
        .get_const(&Name::from_string("_lifted.Wrap_1.bridge"))
        .expect("bridge present");
    assert!(
        crate::inductive::mentions_name(&iff.type_, &Name::from_string("Wrap")),
        "bridge statement must speak the user's original vocabulary"
    );
}

#[test]
fn test_bridge_wrong_statement_is_kernel_rejected() {
    // The MUST-FAIL probe: a mismatched statement with a real proof body
    // must be rejected by the kernel — pinning that bridges are genuinely
    // checked, not structurally accepted.
    let mut env = Environment::new();
    env.init_iff().expect("Iff registers");
    add_base(&mut env);
    add_wrap(&mut env);
    let decl = bad_decl();
    let lift = env.lift_nested_locals(&decl).expect("lift succeeds");
    env.add_inductive(lift.decl.clone())
        .expect("lifted block registers");
    let outcome = env
        .synthesize_local_lift_bridges(&decl, &lift.families)
        .expect("synthesis succeeds");
    let BridgeOutcome::Bridges(decls) = outcome else {
        panic!("fixture must be in scope");
    };
    let Declaration::Theorem {
        name,
        level_params,
        type_,
        value,
    } = decls.into_iter().next().expect("mp emitted first")
    else {
        panic!("bridge must be a Theorem");
    };
    // Tamper: swap the statement's conclusion to `Bad B.b → ...`-shaped
    // nonsense by re-targeting the forall body's domain side.
    let ExprKind::Pi(bi, dom, _body) = &type_.kind else {
        panic!("mp type is a Pi telescope");
    };
    let tampered = Expr::pi(
        *bi,
        (**dom).clone(),
        Expr::arrow(
            Expr::app(cnst("Bad"), cnst("B.b")),
            Expr::app(cnst("Bad"), cnst("B.b")),
        ),
    );
    let err = env.add_decl(Declaration::Theorem {
        name,
        level_params,
        type_: tampered,
        value,
    });
    assert!(
        err.is_err(),
        "a tampered bridge statement must be kernel-rejected"
    );
}

#[test]
fn test_bridge_out_of_scope_without_iff_is_additive() {
    // No Iff in the env: synthesis declines OutOfScope; the lift itself
    // stands (additive stance).
    let mut env = Environment::new();
    add_base(&mut env);
    add_wrap(&mut env);
    let decl = bad_decl();
    let lift = env.lift_nested_locals(&decl).expect("lift succeeds");
    env.add_inductive(lift.decl.clone())
        .expect("lifted block registers");
    let outcome = env
        .synthesize_local_lift_bridges(&decl, &lift.families)
        .expect("declining is not an error");
    assert!(
        matches!(outcome, BridgeOutcome::OutOfScope { .. }),
        "missing Iff must decline, not fail"
    );
    assert!(
        env.get_inductive(&Name::from_string("_lifted.Wrap_1"))
            .is_some(),
        "the lifted family must remain registered"
    );
}

/// Recursive container: `F2ish (R : B → Prop) : B → Prop` with a
/// self-recursive cons — exercises the self-loop IH path in BOTH directions.
#[test]
fn test_bridge_recursive_container_self_loop() {
    let mut env = Environment::new();
    env.init_iff().expect("Iff registers");
    add_base(&mut env);
    let p_ty = Expr::pi(BinderInfo::Default, cnst("B"), prop());
    let f2 = |r: Expr, i: Expr| Expr::app(Expr::app(cnst("F2ish"), r), i);
    let nil_ty = Expr::pi(
        BinderInfo::Default,
        p_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            cnst("B"),
            f2(Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let cons_ty = Expr::pi(
        BinderInfo::Default,
        p_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            cnst("B"),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::bvar(1), Expr::bvar(0)),
                Expr::pi(
                    BinderInfo::Default,
                    f2(Expr::bvar(2), Expr::bvar(1)),
                    f2(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string("F2ish"),
            type_: Expr::pi(
                BinderInfo::Default,
                p_ty,
                Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            ),
            constructors: vec![
                Constructor {
                    name: Name::from_string("F2ish.nil"),
                    type_: nil_ty,
                },
                Constructor {
                    name: Name::from_string("F2ish.cons"),
                    type_: cons_ty,
                },
            ],
        }],
    })
    .expect("F2ish registers");

    // SelfC : B → Prop | mk : (n : B) → F2ish (fun (x : B) => SelfC n) B.b → SelfC n
    let selfc = |a: Expr| Expr::app(cnst("SelfC"), a);
    let capturing = Expr::lam(BinderInfo::Default, cnst("B"), selfc(Expr::bvar(1)));
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            f2(capturing, cnst("B.b")),
            selfc(Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("SelfC"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("SelfC.mk"),
                type_: mk_ty,
            }],
        }],
    };
    let n = lift_and_bridge(&mut env, &decl);
    assert_eq!(n, 3, "three theorems for the single family");
    assert!(
        env.get_const(&Name::from_string("_lifted.F2ish_1.bridge"))
            .is_some(),
        "self-loop family bridge must register"
    );
}

/// Multi-round: the Wrap/Pair2 two-round fixture — round 2's family is
/// referenced from round 1's ctor, exercising cross-family IHs in `mp` and
/// the topo-ordered `bridge_mpr` transport in `mpr`.
#[test]
fn test_bridge_multi_round_cross_family_transport() {
    let mut env = Environment::new();
    env.init_iff().expect("Iff registers");
    add_base(&mut env);
    add_wrap(&mut env);
    // Pair2 (a b : Prop) : Prop | mk : a → b → Pair2 a b
    let pair2 = |q: Expr, r: Expr| Expr::app(Expr::app(cnst("Pair2"), q), r);
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        prop(),
        Expr::pi(
            BinderInfo::Default,
            prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    pair2(Expr::bvar(3), Expr::bvar(2)),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("Pair2"),
            type_: Expr::pi(
                BinderInfo::Default,
                prop(),
                Expr::pi(BinderInfo::Default, prop(), prop()),
            ),
            constructors: vec![Constructor {
                name: Name::from_string("Pair2.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Pair2 registers");

    // Bad2 : B → Prop
    // | step : (n : B) → Wrap (fun (m : B) => Pair2 (Bad2 n) (Bad2 m)) → Bad2 n
    let bad2 = |a: Expr| Expr::app(cnst("Bad2"), a);
    let capturing = Expr::lam(
        BinderInfo::Default,
        cnst("B"),
        pair2(bad2(Expr::bvar(1)), bad2(Expr::bvar(0))),
    );
    let step_ty = Expr::pi(
        BinderInfo::Default,
        cnst("B"),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(cnst("Wrap"), capturing),
            bad2(Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bad2"),
            type_: Expr::pi(BinderInfo::Default, cnst("B"), prop()),
            constructors: vec![Constructor {
                name: Name::from_string("Bad2.step"),
                type_: step_ty,
            }],
        }],
    };
    let n = lift_and_bridge(&mut env, &decl);
    assert_eq!(n, 6, "two families x three theorems");
    for fam in ["_lifted.Wrap_1", "_lifted.Pair2_2"] {
        assert!(
            env.get_const(&Name::from_string(&format!("{fam}.bridge")))
                .is_some(),
            "{fam} bridge must register"
        );
    }
}
