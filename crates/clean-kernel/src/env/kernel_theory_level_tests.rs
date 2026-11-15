// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe levels equal at every assignment that pinned Lean's
//! `is_equivalent` does not equate (`docs/DECISIONS.md` R141's review items,
//! closed for the Lean theories by R150's level algebra):
//!
//! - `axiom LJA.{u,v} : Sort (max (u+1) (max (v+1) (imax (v+1) u)))` with `def
//!   LJB.{u,v} : Sort (max (u+1) (v+1)) := LJA.{u,v}`, and `LJD`: pinned Lean
//!   refuses both (`declaration type mismatch`,
//!   `replay_forged/ReplayForgedLevelJoin`, measured 2026-10-23).
//! - The mutual block `MA.{u,v} : Sort (max (u+1) (v+1))`, `MB.{u,v} : Sort
//!   (max (u+1) (max (v+1) (imax (v+1) u)))`: pinned Lean refuses it
//!   (`mutually inductive types must live in the same universe`; Lean's
//!   `inductive.cpp` compares with `is_equivalent`).
//!
//! `KernelTheory::Lean` and `LeanReference` refuse each, as Lean does.
//! `Extended` admits each: Clean's own level algebra equates the levels, the
//! scoped R2 exception R150 records (every admitted equation holds at every
//! assignment).

use super::*;
use crate::env::Declaration;
use crate::expr::Expr;
use crate::level::{level_arc, Level};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn p(s: &str) -> Level {
    Level::param(name(s))
}

fn s(l: Level) -> Level {
    Level::succ(l)
}

/// Raw constructors: the level as a file stores it.
fn max(a: Level, b: Level) -> Level {
    Level::Max(level_arc(a), level_arc(b))
}

fn imax(a: Level, b: Level) -> Level {
    Level::IMax(level_arc(a), level_arc(b))
}

fn sort(l: Level) -> Expr {
    Expr::sort(l)
}

/// `LJA`'s level: `max (u+1) (max (v+1) (imax (v+1) u))`.
fn l1() -> Level {
    max(s(p("u")), max(s(p("v")), imax(s(p("v")), p("u"))))
}

fn env_with_lja(theory: KernelTheory) -> Environment {
    let mut env = Environment::for_lean_replay();
    env.set_kernel_theory(theory);
    env.add_decl(Declaration::Axiom {
        name: name("LJA"),
        level_params: vec![name("u"), name("v")],
        type_: sort(l1()),
    })
    .expect("LJA is well formed");
    env
}

fn def(n: &str, params: &[&str], type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: name(n),
        level_params: params.iter().map(|p| name(p)).collect(),
        type_,
        value,
        is_reducible: false,
    }
}

fn lja() -> Expr {
    Expr::const_(name("LJA"), vec![p("u"), p("v")])
}

fn lean_theories_refuse(theory: KernelTheory) -> bool {
    match theory {
        KernelTheory::Lean | KernelTheory::LeanReference => true,
        KernelTheory::Extended => false,
    }
}

const THEORIES: [KernelTheory; 3] = [
    KernelTheory::Lean,
    KernelTheory::LeanReference,
    KernelTheory::Extended,
];

/// `LJB : Sort (max (u+1) (v+1)) := LJA` and `LJD.{v,w} : Sort (succ (max v
/// (succ w))) := Sort (max (max v (imax v w)) (succ w))`: refused under the
/// Lean theories, as pinned Lean refuses them, and admitted under `Extended`;
/// the control `LJC : Sort <LJA's level> := LJA` is admitted in every theory.
#[test]
fn test_level_join_equations_follow_lean_under_the_lean_theories() {
    let ljb = def("LJB", &["u", "v"], sort(max(s(p("u")), s(p("v")))), lja());
    let ljc = def("LJC", &["u", "v"], sort(l1()), lja());
    let ljd = def(
        "LJD",
        &["v", "w"],
        sort(s(max(p("v"), s(p("w"))))),
        sort(max(max(p("v"), imax(p("v"), p("w"))), s(p("w")))),
    );
    for theory in THEORIES {
        let env = env_with_lja(theory);
        env.check_decl_readonly_strict(&ljc)
            .unwrap_or_else(|e| panic!("{theory:?}: the control LJC must be admitted: {e:?}"));
        for decl in [&ljb, &ljd] {
            let verdict = env.check_decl_readonly_strict(decl);
            assert_eq!(
                verdict.is_err(),
                lean_theories_refuse(theory),
                "{theory:?}: {decl:?}: {verdict:?}"
            );
        }
    }
}

/// `MA`/`MB` above, each with one nullary constructor, through the kernel's
/// own admission over Lean's world: refused under the Lean theories by the
/// mutual-universe check, as pinned Lean refuses the block, and admitted under
/// `Extended`. The control, both at `max (u+1) (v+1)`, is admitted in every
/// theory.
#[test]
fn test_mutual_universe_join_follows_lean_under_the_lean_theories() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    let ma_level = max(s(p("u")), s(p("v")));
    let block = |mb_level: Level| InductiveDecl {
        level_params: vec![name("u"), name("v")],
        num_params: 0,
        types: vec![
            InductiveType {
                name: name("MA"),
                type_: sort(ma_level.clone()),
                constructors: vec![Constructor {
                    name: name("MA.a"),
                    type_: Expr::const_(name("MA"), vec![p("u"), p("v")]),
                }],
            },
            InductiveType {
                name: name("MB"),
                type_: sort(mb_level),
                constructors: vec![Constructor {
                    name: name("MB.b"),
                    type_: Expr::const_(name("MB"), vec![p("u"), p("v")]),
                }],
            },
        ],
    };
    for theory in THEORIES {
        let admit = |mb_level: Level| {
            let mut env = Environment::for_lean_replay();
            env.set_kernel_theory(theory);
            env.add_inductive_core(block(mb_level))
        };
        admit(ma_level.clone())
            .unwrap_or_else(|e| panic!("{theory:?}: the control block must be admitted: {e:?}"));
        match admit(l1()) {
            Err(e) => {
                assert!(lean_theories_refuse(theory), "{theory:?}: refused: {e:?}");
                assert!(
                    format!("{e:?}").contains("different universe"),
                    "{theory:?}: refused, but not by the mutual-universe check: {e:?}"
                );
            }
            Ok(_) => assert!(!lean_theories_refuse(theory), "{theory:?}: admitted"),
        }
    }
}
