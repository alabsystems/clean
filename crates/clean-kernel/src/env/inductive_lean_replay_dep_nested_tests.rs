// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for a block nested through a DEPENDENT container whose family
//! argument is a lambda: `inductive SGS | mk : DBox Nat (fun _ => Nat → SGS)
//! → SGS`, with `structure DBox (α : Type) (β : α → Type) where a : α; b : β a`.
//!
//! Lean's nested elimination instantiates the container's parameters with
//! `instantiate_rev`, which takes no β step (`inductive.cpp`
//! `instantiate_pi_params`, v4.30.0-rc2), so the auxiliary `DBox.mk`'s field
//! is the redex `(fun _ => Nat → SGS) a`, not a Pi. Lean stores
//! `isReflexive := false` for the block and keeps the redex in every
//! generated recursor; it reads through it only where it calls `whnf`
//! (positivity, `is_rec_argument`, the induction hypotheses). Pinned Lean's
//! own `.olean` of the same shapes over `Sigma`, `PSigma` and a user `DBox`
//! is `replay_forged/ReplayHonestDepNested` (measured 2026-10-23).

use super::*;
use crate::env::Declaration;
use crate::expr::ExprKind;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn arrow(dom: Expr, cod: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, cod)
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

/// `structure DBox (α : Type) (β : α → Type) where a : α; b : β a`.
fn dbox_decl() -> InductiveDecl {
    let fam_ty = |alpha: Expr| arrow(alpha, Expr::type_());
    let mk = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            fam_ty(Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                    Expr::apps(c("DBox"), [Expr::bvar(3), Expr::bvar(2)]),
                ),
            ),
        ),
    );
    InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: name("DBox"),
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                arrow(fam_ty(Expr::bvar(0)), Expr::type_()),
            ),
            constructors: vec![Constructor {
                name: name("DBox.mk"),
                type_: mk,
            }],
        }],
    }
}

/// `DBox Nat fam`.
fn dbox(fam: Expr) -> Expr {
    Expr::apps(c("DBox"), [c("Nat"), fam])
}

/// `inductive ty | mk : field → ty`.
fn wrap(ty: &str, field: Expr) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name(ty),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name(&format!("{ty}.mk")),
                type_: arrow(field, c(ty)),
            }],
        }],
    }
}

/// `fun _ : Nat => Nat → ty` (`SGS`) and `fun n : Nat => Fin n → ty` (`SG`).
fn families(ty: &str) -> [(&'static str, Expr); 2] {
    [
        ("const", lam(c("Nat"), arrow(c("Nat"), c(ty)))),
        (
            "dependent",
            lam(c("Nat"), arrow(Expr::app(c("Fin"), Expr::bvar(0)), c(ty))),
        ),
    ]
}

fn env_with(blocks: Vec<InductiveDecl>) -> Environment {
    let mut env = Environment::with_prelude();
    for block in blocks {
        env.add_inductive_core(block)
            .expect("an honest block is admitted");
    }
    env
}

/// Whether `e` contains a β-redex `(fun x => b) a` anywhere.
fn has_beta_redex(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::App(f, a) => {
            matches!(f.kind, ExprKind::Lam(..)) || has_beta_redex(f) || has_beta_redex(a)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            has_beta_redex(ty) || has_beta_redex(body)
        }
        _ => false,
    }
}

/// The `n`-th Pi domain of `e` (0-based).
fn pi_domain(e: &Expr, n: usize) -> Expr {
    let mut cursor = e;
    for _ in 0..n {
        let ExprKind::Pi(_, _, body) = &cursor.kind else {
            panic!("fewer than {n} binders: {e}");
        };
        cursor = body;
    }
    let ExprKind::Pi(_, domain, _) = &cursor.kind else {
        panic!("no binder {n}: {e}");
    };
    (**domain).clone()
}

fn pi_count(e: &Expr) -> usize {
    let mut cursor = e;
    let mut n = 0;
    while let ExprKind::Pi(_, _, body) = &cursor.kind {
        cursor = body;
        n += 1;
    }
    n
}

/// Lean stores `isReflexive := false` for these blocks: the auxiliary field
/// is a redex, not a Pi, until β (pinned Lean: `SGS`, `SG`, `SGP`, `DB` in
/// `ReplayHonestDepNested`). β-normalizing the auxiliary types gave `true`.
#[test]
fn test_add_inductive_dependent_container_nested_block_is_not_reflexive() {
    for (shape, fam) in families("SGS") {
        let env = env_with(vec![dbox_decl(), wrap("SGS", dbox(fam))]);
        let sgs = env.get_inductive(&name("SGS")).expect("resident");
        assert!(sgs.is_recursive, "{shape}: {sgs:?}");
        assert!(sgs.is_nested, "{shape}: {sgs:?}");
        assert!(
            !sgs.is_reflexive,
            "{shape}: Lean's isReflexive is false: {sgs:?}"
        );
    }
}

/// Lean's generated recursors keep the redex as the field's binder type and
/// read through it, by `whnf`, for the induction hypothesis: `SGS.rec_1`'s
/// `DBox.mk` minor premise is `(a : Nat) → (b : (fun _ => Nat → SGS) a) →
/// ((n : Nat) → motive_1 (b n)) → motive_2 (DBox.mk Nat _ a b)`.
#[test]
fn test_add_inductive_dependent_container_recursors_keep_leans_redex() {
    for (shape, fam) in families("SGS") {
        let env = env_with(vec![dbox_decl(), wrap("SGS", dbox(fam))]);
        for rec in ["SGS.rec", "SGS.rec_1"] {
            let rv = env.get_recursor(&name(rec)).expect("resident");
            assert!(has_beta_redex(&rv.type_), "{shape} {rec}: {}", rv.type_);
            // motive_1, motive_2, the `SGS.mk` minor, then the `DBox.mk` minor.
            let minor = pi_domain(&rv.type_, 3);
            assert_eq!(
                pi_count(&minor),
                3,
                "{shape} {rec}: fields a, b and an IH: {minor}"
            );
            let field = pi_domain(&minor, 1);
            assert!(
                matches!(&field.kind, ExprKind::App(f, _) if matches!(f.kind, ExprKind::Lam(..))),
                "{shape} {rec}: the field keeps Lean's redex: {field}"
            );
            let ih = pi_domain(&minor, 2);
            assert!(
                matches!(ih.kind, ExprKind::Pi(..)),
                "{shape} {rec}: the IH reads through the redex to `Nat → SGS`: {ih}"
            );
            // Each recursor's one rule: `SGS.rec`'s for `SGS.mk`, `SGS.rec_1`'s
            // for the container constructor; both lambdas bind the minor premises,
            // the `DBox.mk` one with its redex-typed field.
            let ctor = if rec == "SGS.rec" {
                "SGS.mk"
            } else {
                "DBox.mk"
            };
            let rule = rv
                .rules
                .iter()
                .find(|r| r.constructor_name == name(ctor))
                .unwrap_or_else(|| panic!("{shape} {rec}: no rule for {ctor}"));
            assert!(has_beta_redex(&rule.rhs), "{shape} {rec}: {}", rule.rhs);
        }
    }
}

/// The rules compute through the redex-typed field: `SJ | leaf | node :
/// DBox Nat (fun _ => SJ) → SJ` (a single-level stand-in for the redex in
/// `Lean.Json`'s map field), and its depth function
/// through `SJ.rec` evaluates `SJ.node ⟨0, SJ.leaf⟩` to `1`.
#[test]
fn test_dependent_container_nested_recursor_computes_through_the_redex_field() {
    let fam = lam(c("Nat"), c("SJ"));
    let sj = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("SJ"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name("SJ.leaf"),
                    type_: c("SJ"),
                },
                Constructor {
                    name: name("SJ.node"),
                    type_: arrow(dbox(fam.clone()), c("SJ")),
                },
            ],
        }],
    };
    let env = env_with(vec![dbox_decl(), sj]);
    assert!(
        !env.get_inductive(&name("SJ"))
            .expect("resident")
            .is_reflexive
    );
    let one = Level::succ(Level::zero());
    let nat = c("Nat");
    let depth = Expr::apps(
        Expr::const_(name("SJ.rec"), vec![one.clone()]),
        [
            lam(c("SJ"), nat.clone()),
            lam(dbox(fam.clone()), nat.clone()),
            Expr::nat_lit(0),
            lam(
                dbox(fam.clone()),
                lam(nat.clone(), Expr::app(c("Nat.succ"), Expr::bvar(0))),
            ),
            lam(nat.clone(), lam(c("SJ"), lam(nat.clone(), Expr::bvar(0)))),
            Expr::app(
                c("SJ.node"),
                Expr::apps(
                    c("DBox.mk"),
                    [nat.clone(), fam, Expr::nat_lit(0), c("SJ.leaf")],
                ),
            ),
        ],
    );
    let ty = Expr::apps(
        Expr::const_(name("Eq"), vec![one.clone()]),
        [nat.clone(), depth, Expr::nat_lit(1)],
    );
    let value = Expr::apps(
        Expr::const_(name("Eq.refl"), vec![one]),
        [nat, Expr::nat_lit(1)],
    );
    env.check_decl_readonly_strict(&Declaration::Theorem {
        name: name("sj_depth_one"),
        level_params: vec![],
        type_: ty,
        value,
    })
    .expect("SJ.rec computes through both recursors' rules");
}

/// A redex that exposes a NEGATIVE occurrence is still refused: the field
/// `(fun _ => Bad → Nat) a` reads, through β, as `Bad → Nat`.
#[test]
fn test_dependent_container_negative_occurrence_is_refused() {
    let mut env = env_with(vec![dbox_decl()]);
    let fam = lam(c("Nat"), arrow(c("Bad"), c("Nat")));
    let err = env
        .add_inductive_core(wrap("Bad", dbox(fam)))
        .expect_err("a negative occurrence behind a redex is refused");
    assert!(
        format!("{err:?}").contains("NonPositive"),
        "refused as non-positive: {err:?}"
    );
}

/// The replay compares the stored flag with Lean's regenerated one: a stored
/// `isReflexive := true` (`replay_forged/ReplayForgedDepNestedRefl`, what a
/// β-reducing checker computes) is refused, and the honest `false` replays.
#[test]
fn test_lean_replay_dependent_container_block_compares_the_reflexive_flag() {
    for (shape, fam) in families("SGS") {
        let mut env = env_with(vec![dbox_decl(), wrap("SGS", dbox(fam))]);
        env.lean_replay_inductive_block(&[name("SGS")])
            .unwrap_or_else(|e| panic!("{shape}: the honest block replays to itself: {e}"));
        env.inductives
            .get_mut(&name("SGS"))
            .expect("resident")
            .is_reflexive = true;
        assert_eq!(
            env.lean_replay_inductive_block(&[name("SGS")]),
            Err(InductiveReplayMismatch::InvalidInductive {
                name: name("SGS"),
                field: "reflexive flag (isReflexive)"
            }),
            "{shape}"
        );
    }
}
