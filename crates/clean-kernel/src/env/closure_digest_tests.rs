// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.7(a): the closure digest names what a declaration MEANS here — every
//! declaration it reaches, byte for byte — and nothing it does not reach.
//!
//! The roadmap's two named unit tests are
//! [`renaming_an_unrelated_declaration_leaves_the_digest`] and
//! [`changing_a_transitive_dependency_moves_the_digest`]. The rest pin the
//! injectivity the roadmap's Risk calls silent when it breaks: levels, binder
//! data, literals, reducibility, constructor sets and the root are each in the
//! preimage, and an incomplete closure is refused rather than digested.

use std::collections::HashMap;
use std::sync::Arc;

use super::*;
use crate::env::{ConstantInfo, ConstantSource, Declaration};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// `inductive <ty> | <ctor> …` — a constructor-only enumeration.
fn enumeration(ty: &str, ctors: &[&str]) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n(ty),
            type_: Expr::type_(),
            constructors: ctors
                .iter()
                .map(|ctor| Constructor {
                    name: n(&format!("{ty}.{ctor}")),
                    type_: c(ty),
                })
                .collect(),
        }],
    }
}

fn def(env: &mut Environment, name: &str, type_: Expr, value: Expr, is_reducible: bool) {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_,
        value,
        is_reducible,
    })
    .unwrap_or_else(|e| panic!("`{name}` is well-typed: {e:?}"));
}

/// Which of the fixture's declarations to include, and how.
#[derive(Clone, Copy)]
struct Fx {
    /// `f`'s value: `T.a` (`false`) or `T.b` (`true`).
    f_is_b: bool,
    /// Whether `f` unfolds eagerly.
    f_reducible: bool,
    /// The unrelated declaration's name (`None`: not declared at all).
    unrelated: Option<&'static str>,
    /// Declare the unrelated declaration BEFORE `f` and `g`.
    unrelated_first: bool,
    /// Give `T` a third constructor `T.c`.
    third_ctor: bool,
}

const BASE: Fx = Fx {
    f_is_b: false,
    f_reducible: false,
    unrelated: Some("u"),
    unrelated_first: false,
    third_ctor: false,
};

/// `inductive T | a | b`, `f : T := T.a`, `g : T := f`, `h : Type := T`, and
/// an unrelated `u : T := T.b` that neither reaches.
fn env_of(fx: Fx) -> Environment {
    let mut env = Environment::new();
    let ctors: &[&str] = if fx.third_ctor {
        &["a", "b", "c"]
    } else {
        &["a", "b"]
    };
    env.add_inductive(enumeration("T", ctors))
        .expect("the enumeration is a valid inductive");
    let unrelated = |env: &mut Environment| {
        if let Some(name) = fx.unrelated {
            def(env, name, c("T"), c("T.b"), false);
        }
    };
    if fx.unrelated_first {
        unrelated(&mut env);
    }
    let f_value = if fx.f_is_b { c("T.b") } else { c("T.a") };
    def(&mut env, "f", c("T"), f_value, fx.f_reducible);
    def(&mut env, "g", c("T"), c("f"), false);
    def(&mut env, "h", Expr::type_(), c("T"), false);
    if !fx.unrelated_first {
        unrelated(&mut env);
    }
    env
}

fn digest(env: &Environment, name: &str) -> [u8; 32] {
    env.closure_digest(&n(name))
        .unwrap_or_else(|e| panic!("`{name}` has a closure digest: {e}"))
}

fn closure_names(env: &Environment, name: &str) -> Vec<String> {
    let mut names: Vec<String> = env
        .dependency_closure(&n(name))
        .expect("closed")
        .iter()
        .map(ToString::to_string)
        .collect();
    names.sort();
    names
}

#[test]
fn closure_is_exactly_the_reached_declarations() {
    let env = env_of(BASE);
    // `g` reaches `f`, `f` reaches `T.a`, a constructor reaches its type, and
    // a type reaches every constructor. The unrelated `u` and `h`, and the
    // recursor / auxiliary definitions nothing mentions, are outside it.
    assert_eq!(closure_names(&env, "g"), ["T", "T.a", "T.b", "f", "g"]);
    assert_eq!(closure_names(&env, "h"), ["T", "T.a", "T.b", "h"]);
}

#[test]
fn digest_is_deterministic_and_independent_of_insertion_order() {
    let env = env_of(BASE);
    assert_eq!(digest(&env, "g"), digest(&env, "g"));
    assert_eq!(digest(&env, "g"), digest(&env.clone(), "g"));
    let reordered = env_of(Fx {
        unrelated_first: true,
        ..BASE
    });
    assert_eq!(digest(&env, "g"), digest(&reordered, "g"));
}

/// Roadmap WS6.7 Tests, mutation control: renaming an unrelated constant does
/// not change the digest of `f` (here `g`, which reaches `f`) — nor does
/// dropping it.
#[test]
fn renaming_an_unrelated_declaration_leaves_the_digest() {
    let base = digest(&env_of(BASE), "g");
    let renamed = env_of(Fx {
        unrelated: Some("v"),
        ..BASE
    });
    assert_eq!(base, digest(&renamed, "g"));
    let absent = env_of(Fx {
        unrelated: None,
        ..BASE
    });
    assert_eq!(base, digest(&absent, "g"));
}

/// Roadmap WS6.7 Tests, mutation control: changing a TRANSITIVE dependency
/// moves the digest. `g`'s own declaration is byte-identical in both
/// environments; only `f`, which `g` mentions, differs.
#[test]
fn changing_a_transitive_dependency_moves_the_digest() {
    let base = env_of(BASE);
    let moved = env_of(Fx {
        f_is_b: true,
        ..BASE
    });
    assert_eq!(
        base.get_const(&n("g")).map(|g| g.value.clone()),
        moved.get_const(&n("g")).map(|g| g.value.clone()),
        "control: `g` itself is unchanged"
    );
    assert_ne!(digest(&base, "g"), digest(&moved, "g"));
    // ... and a declaration that does not reach `f` keeps its digest.
    assert_eq!(digest(&base, "h"), digest(&moved, "h"));
}

#[test]
fn reducibility_of_a_dependency_is_in_the_preimage() {
    let base = digest(&env_of(BASE), "g");
    let reducible = env_of(Fx {
        f_reducible: true,
        ..BASE
    });
    assert_ne!(base, digest(&reducible, "g"));
}

/// A type means what its constructors say: adding one moves the digest of
/// every definition that mentions the type, even one that names no
/// constructor.
#[test]
fn a_new_constructor_moves_every_mention_of_the_type() {
    let base = env_of(BASE);
    let wider = env_of(Fx {
        third_ctor: true,
        ..BASE
    });
    assert_ne!(digest(&base, "h"), digest(&wider, "h"));
    assert!(closure_names(&wider, "h").contains(&"T.c".to_string()));
}

/// A constructor and its type have the SAME closure set; the root is what
/// tells their digests apart.
#[test]
fn the_root_is_in_the_preimage() {
    let env = env_of(BASE);
    assert_eq!(closure_names(&env, "T"), closure_names(&env, "T.a"));
    assert_ne!(digest(&env, "T"), digest(&env, "T.a"));
}

/// Binder data rides in the preimage: `fun (x : T) => x` and
/// `fun {x : T} => x` are different terms, whatever the kernel's judgment.
#[test]
fn binder_info_is_in_the_preimage() {
    let with_binder = |info: BinderInfo| {
        let mut env = env_of(BASE);
        def(
            &mut env,
            "idT",
            Expr::arrow(c("T"), c("T")),
            Expr::lam(info, c("T"), Expr::bvar(0)),
            false,
        );
        digest(&env, "idT")
    };
    assert_ne!(
        with_binder(BinderInfo::Default),
        with_binder(BinderInfo::Implicit)
    );
}

/// Universe levels ride in the preimage: the same declaration at two
/// different levels digests differently.
#[test]
fn levels_are_in_the_preimage() {
    // `s : Sort (l+1) := Sort l`, at two different universe levels. (Two
    // spellings of ONE level are no control here: `Level::max` normalizes
    // `max 1 1` to `1` at construction, so they are the same stored value.)
    let with_level = |level: Level| {
        let mut env = Environment::new();
        def(
            &mut env,
            "s",
            Expr::sort(Level::succ(level.clone())),
            Expr::sort(level),
            false,
        );
        digest(&env, "s")
    };
    assert_ne!(
        with_level(Level::zero()),
        with_level(Level::succ(Level::zero()))
    );
}

/// Literals ride in the preimage.
#[test]
fn literals_are_in_the_preimage() {
    let with_literal = |k: u64| {
        let mut env = Environment::new();
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: n("Nat"),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: n("Nat.zero"),
                        type_: c("Nat"),
                    },
                    Constructor {
                        name: n("Nat.succ"),
                        type_: Expr::arrow(c("Nat"), c("Nat")),
                    },
                ],
            }],
        })
        .expect("Nat is a valid inductive");
        def(&mut env, "k", c("Nat"), Expr::nat_lit(k), false);
        digest(&env, "k")
    };
    assert_ne!(with_literal(1), with_literal(2));
    assert_eq!(with_literal(7), with_literal(7));
}

#[test]
fn an_undeclared_root_is_refused() {
    let env = env_of(BASE);
    assert_eq!(
        env.closure_digest(&n("nope")),
        Err(ClosureDigestError::UnknownDeclaration { name: n("nope") })
    );
}

/// A lazy constant source the kernel does not type-check on insertion — the
/// only way to hold a declaration whose closure is not closed.
#[derive(Debug, Default)]
struct MapSource(HashMap<Name, ConstantInfo>);

impl ConstantSource for MapSource {
    fn get(&self, name: &Name) -> Option<&ConstantInfo> {
        self.0.get(name)
    }

    fn contains(&self, name: &Name) -> bool {
        self.0.contains_key(name)
    }
}

/// A lazily served member is digested exactly as the kernel reads it: the
/// same record served lazily and declared eagerly gives one digest.
#[test]
fn a_lazily_served_member_digests_like_an_eager_one() {
    let eager = env_of(BASE);
    // `lazy` declares everything `g` reaches eagerly, but not `g` itself:
    // `g`'s eager record is served through the lazy source instead.
    let mut lazy = Environment::new();
    lazy.add_inductive(enumeration("T", &["a", "b"]))
        .expect("valid inductive");
    def(&mut lazy, "f", c("T"), c("T.a"), false);
    assert!(
        lazy.get_const(&n("g")).is_none(),
        "control: `g` is not eager"
    );
    let g = eager.get_const(&n("g")).expect("g").clone();
    lazy.set_constant_source(Arc::new(MapSource(HashMap::from([(n("g"), g)]))));
    assert_eq!(digest(&eager, "g"), digest(&lazy, "g"));
}

/// A member that mentions an undeclared name is REFUSED, never digested
/// partially — naming the member and the missing name.
#[test]
fn a_dangling_reference_is_refused() {
    let mut env = env_of(BASE);
    let ghost = ConstantInfo::new(n("ghost"), vec![], c("T"), Some(c("missing")), false);
    env.set_constant_source(Arc::new(MapSource(HashMap::from([(n("ghost"), ghost)]))));
    assert_eq!(
        env.closure_digest(&n("ghost")),
        Err(ClosureDigestError::DanglingReference {
            member: n("ghost"),
            missing: n("missing"),
        })
    );
    // A root that does not reach the ghost is unaffected.
    assert!(env.closure_digest(&n("g")).is_ok());
}
