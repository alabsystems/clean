// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR1 slice 1: the reference entry's tripwires (`clean_kernel::TRIPWIRE_AXIOMS`,
//! `clean_kernel::is_tripwire`).
//!
//! Lean `Init` declares `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`,
//! `Lean.trustCompiler` and the compiler's `lc*` constants, and Clean's
//! `with_prelude` declares the trust markers `sorry`, `trustedArith` and
//! `trustedAy`; no closure through the entry may reach one. For every
//! tripwire name, each way a closure can reach it is refused with
//! `ReferenceRefusal::Tripwire` naming it: a direct citation in `add_checked`,
//! a direct citation in `check_closed_term`, a citation of a base constant
//! whose value reaches it one or three hops away, a citation of a base
//! inductive type (plain or indexed) only one of whose constructors reaches
//! it, a citation of that type's recursor, a constructor type in
//! `add_inductive_checked`, and declaring it through the entry. The control
//! runs every one of those shapes with a non-tripwire axiom of the same type
//! (and with `lcm`, which is not a compiler constant): since KR1 increment 3
//! (R143) such an axiom is outside Ax0, so every shape refuses it as
//! `OutsideAx0` naming it, never as a tripwire; and the same shapes over a
//! DEFINITION of that name are all accepted, so the refusals are the axiom's. The pinned-`Init` versions (the real
//! declarations, through a base built by the entry) are in
//! `crates/clean-olean/tests/reference_base_init.rs`.

use clean_kernel::{
    is_tripwire, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, Name, ReferenceKernel, ReferenceRefusal, TRIPWIRE_AXIOMS,
};

/// Clean's own trust markers (each `{α : Sort u} → α` in `with_prelude`).
const CLEAN_TRUST_MARKERS: [&str; 3] = ["sorry", "trustedArith", "trustedAy"];

/// One-type inductive block.
fn block(ty: &str, type_: Expr, ctors: Vec<(&str, Expr)>) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name(ty),
            type_,
            constructors: ctors
                .into_iter()
                .map(|(n, t)| Constructor {
                    name: name(n),
                    type_: t,
                })
                .collect(),
        }],
    }
}

fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, a, b)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn def(n: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: name(n),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    }
}

/// A base holding `axiom ax : Prop`, `def kr1_wrap : Prop := ax`, a chain
/// `kr1_wrap3 := kr1_wrap2 := kr1_wrap`, an inductive `KR1PT : Prop` whose
/// only constructor takes an `ax`, and an indexed family `KR1PI : Prop →
/// Prop` whose only constructor is `KR1PI ax`, all through `add_decl` /
/// `add_inductive_core`. Nothing but the constructors' types cites `ax` in
/// the two inductives.
fn base_with(ax: &str, stand_in: StandIn) -> Environment {
    let mut env = Environment::default();
    env.add_decl(stand_in.declaration(ax)).expect("stand-in");
    env.add_decl(def("kr1_wrap", Expr::prop(), c(ax)))
        .expect("wrapper");
    env.add_decl(def("kr1_wrap2", Expr::prop(), c("kr1_wrap")))
        .expect("wrapper 2");
    env.add_decl(def("kr1_wrap3", Expr::prop(), c("kr1_wrap2")))
        .expect("wrapper 3");
    env.add_inductive_core(block(
        "KR1PT",
        Expr::prop(),
        vec![("KR1PT.mk", arrow(c(ax), c("KR1PT")))],
    ))
    .expect("KR1PT");
    env.add_inductive_core(block(
        "KR1PI",
        arrow(Expr::prop(), Expr::prop()),
        vec![("KR1PI.mk", Expr::app(c("KR1PI"), c(ax)))],
    ))
    .expect("KR1PI");
    env
}

/// `∀ p : Prop, p`, a closed proposition citing nothing.
fn all_props() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
}

/// How the name every shape reaches is declared.
#[derive(Clone, Copy)]
enum StandIn {
    /// `axiom ax : Prop`.
    Axiom,
    /// `def ax : Prop := ∀ p : Prop, p` (R143's positive control).
    Definition,
}

impl StandIn {
    fn declaration(self, ax: &str) -> Declaration {
        match self {
            StandIn::Axiom => Declaration::Axiom {
                name: name(ax),
                level_params: vec![],
                type_: Expr::prop(),
            },
            StandIn::Definition => def(ax, Expr::prop(), all_props()),
        }
    }
}

/// Every shape, for one axiom name. `Ok(())` when all are accepted; the
/// first refusal otherwise, with the shape that refused.
fn run_shapes(ax: &str, stand_in: StandIn) -> Vec<(&'static str, Result<(), ReferenceRefusal>)> {
    let mut out = Vec::new();
    let mut k = ReferenceKernel::new(base_with(ax, stand_in)).expect("the base itself is a base");
    out.push((
        "add_checked cites it",
        k.add_checked(def("kr1_direct", Expr::prop(), c(ax)))
            .map(|_| ()),
    ));
    out.push((
        "check_closed_term cites it",
        k.check_closed_term(&Expr::prop(), &c(ax)).map(|_| ()),
    ));
    out.push((
        "cites a base constant that reaches it",
        k.add_checked(def("kr1_through_wrap", Expr::prop(), c("kr1_wrap")))
            .map(|_| ()),
    ));
    out.push((
        "cites a base constant three hops from it",
        k.add_checked(def("kr1_through_wrap3", Expr::prop(), c("kr1_wrap3")))
            .map(|_| ()),
    ));
    out.push((
        "check_closed_term cites a base inductive whose constructor reaches it",
        k.check_closed_term(&Expr::prop(), &c("KR1PT")).map(|_| ()),
    ));
    out.push((
        "add_checked cites a base inductive whose constructor reaches it",
        k.add_checked(def("kr1_through_pt", Expr::prop(), c("KR1PT")))
            .map(|_| ()),
    ));
    out.push((
        "cites an indexed base family whose constructor reaches it",
        k.check_closed_term(&Expr::prop(), &Expr::app(c("KR1PI"), all_props()))
            .map(|_| ()),
    ));
    let rec = k
        .environment()
        .get_recursor(&name("KR1PT.rec"))
        .expect("KR1PT.rec")
        .clone();
    let levels = vec![Level::zero(); rec.level_params.len()];
    let rec_ty = rec
        .type_
        .instantiate_level_params_direct(&rec.level_params, &levels);
    out.push((
        "cites a base recursor whose type reaches it",
        k.check_closed_term(&rec_ty, &Expr::const_(name("KR1PT.rec"), levels))
            .map(|_| ()),
    ));
    out.push((
        "a constructor type cites it",
        k.add_inductive_checked(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: name("KR1Box"),
                type_: Expr::prop(),
                constructors: vec![Constructor {
                    name: name("KR1Box.mk"),
                    type_: Expr::pi(BinderInfo::Default, c(ax), c("KR1Box")),
                }],
            }],
        })
        .map(|_| ()),
    ));
    let mut fresh = ReferenceKernel::new(Environment::default()).expect("empty base");
    out.push((
        "declared through the entry",
        fresh.add_checked(stand_in.declaration(ax)).map(|_| ()),
    ));
    out
}

#[test]
fn test_every_tripwire_is_refused_on_every_path_and_a_plain_axiom_is_not() {
    let mut tripwires: Vec<&str> = TRIPWIRE_AXIOMS.to_vec();
    tripwires.extend(CLEAN_TRUST_MARKERS);
    // The prefix rule: a compiler constant not yet listed.
    tripwires.push("lcFutureConstant");
    for tw in tripwires {
        assert!(is_tripwire(&name(tw)), "{tw}");
        for (shape, result) in run_shapes(tw, StandIn::Axiom) {
            match result {
                Err(ReferenceRefusal::Tripwire { reached, .. }) => {
                    assert_eq!(reached, name(tw), "{tw}: {shape}");
                }
                other => panic!("{tw}: {shape}: expected a tripwire refusal, got {other:?}"),
            }
        }
    }
    // Controls: the same shapes, a non-tripwire axiom (outside Ax0 since
    // R143, so refused as that and not as a tripwire), and a definition of
    // the same name (accepted on every shape).
    for control in [
        "kr1_control_axiom",
        "lcm",
        "Lean.ofReduceBoolish",
        "Nat.lcProof",
    ] {
        assert!(!is_tripwire(&name(control)), "{control}");
        for (shape, result) in run_shapes(control, StandIn::Axiom) {
            match result {
                Err(ReferenceRefusal::OutsideAx0 { reached, .. }) => {
                    assert_eq!(reached, name(control), "{control}: {shape}");
                }
                other => panic!("{control}: {shape}: expected OutsideAx0, got {other:?}"),
            }
        }
        for (shape, result) in run_shapes(control, StandIn::Definition) {
            assert!(result.is_ok(), "{control} (def): {shape}: {result:?}");
        }
    }
}

/// Default prelude admission markers stay absent after F3, while the
/// explicitly requested admission fragment contains their actual signatures.
/// Both bases refuse every marker through the direct and declaration entries;
/// the opt-in case keeps the well-typed closed-False controls. True.intro is
/// accepted over each same base, so these controls do not merely refuse all.
#[test]
fn test_trust_markers_are_refused_over_with_prelude() {
    for opt_in in [false, true] {
        let mut env = Environment::with_prelude();
        if opt_in {
            env.init_admission_stub_theory()
                .expect("explicit admission fragment fixture");
        }
        let mut k =
            ReferenceKernel::new(env).expect("quarantined markers keep the base admissible");
        let false_ = c("False");
        for marker in ["sorry", "sorryAx", "trustedArith", "trustedAy"] {
            assert_eq!(
                k.environment().get_const(&name(marker)).is_some(),
                opt_in,
                "{marker}: admission markers belong only to the explicit fragment"
            );
            let head = Expr::app(
                Expr::const_(name(marker), vec![Level::zero()]),
                false_.clone(),
            );
            let val = if marker == "sorryAx" {
                Expr::app(head, c("Bool.false"))
            } else {
                head
            };
            match k.check_closed_term(&false_, &val) {
                Err(ReferenceRefusal::Tripwire { reached, .. }) => {
                    assert_eq!(reached, name(marker), "{marker}, opt_in={opt_in}");
                }
                other => panic!("{marker}, opt_in={opt_in}: a closed proof of False: {other:?}"),
            }
            match k.add_checked(Declaration::Theorem {
                name: name(&format!("kr1_probe_false_{marker}")),
                level_params: vec![],
                type_: false_.clone(),
                value: val,
            }) {
                Err(ReferenceRefusal::Tripwire { reached, .. }) => {
                    assert_eq!(reached, name(marker), "{marker}, opt_in={opt_in}");
                }
                other => panic!("{marker}, opt_in={opt_in}: theorem False: {other:?}"),
            }
        }
        k.check_closed_term(&c("True"), &c("True.intro"))
            .expect("control: True.intro over the same entry");
    }
}

/// A tripwire the base does not hold is still refused by name, before the
/// kernel sees an unknown constant (the direct name check in `check_terms`,
/// which the base's taint map cannot cover). Control: an absent
/// non-tripwire name is the kernel's refusal, not a tripwire.
#[test]
fn test_a_tripwire_absent_from_the_base_is_refused_by_name() {
    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    for tw in ["sorryAx", "lcFutureConstant", "trustedAy"] {
        match k.check_closed_term(&Expr::prop(), &c(tw)) {
            Err(ReferenceRefusal::Tripwire { reached, .. }) => assert_eq!(reached, name(tw)),
            other => panic!("{tw}: {other:?}"),
        }
        match k.add_checked(def("kr1_cites_absent", Expr::prop(), c(tw))) {
            Err(ReferenceRefusal::Tripwire { reached, .. }) => assert_eq!(reached, name(tw)),
            other => panic!("{tw}: {other:?}"),
        }
    }
    let err = k
        .check_closed_term(&Expr::prop(), &c("kr1_absent"))
        .expect_err("an unknown constant");
    assert!(
        matches!(err, ReferenceRefusal::Kernel(_)),
        "control: {err:?}"
    );
}

/// An inductive block refuses when a member's NAME is a tripwire, even
/// though no expression in the block cites it: a constructor named `lcKR1`
/// or `trustedAy`, a type named `sorryAx`. Control: the same blocks with
/// ordinary names are admitted.
#[test]
fn test_an_inductive_member_named_as_a_tripwire_is_refused() {
    let cases: [(&str, &str, Option<&str>); 3] = [
        ("KR1Lc", "lcKR1", None),
        ("KR1Ty", "trustedAy", None),
        ("sorryAx", "sorryAx.mk", Some("sorryAx")),
    ];
    for (ty, ctor, type_named) in cases {
        let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
        let err = k
            .add_inductive_checked(block(ty, Expr::prop(), vec![(ctor, c(ty))]))
            .expect_err("a tripwire-named member");
        let want = name(type_named.unwrap_or(ctor));
        assert!(
            matches!(&err, ReferenceRefusal::Tripwire { reached, .. } if *reached == want),
            "{ty}/{ctor}: {err:?}"
        );
        assert!(k.environment().get_inductive(&name(ty)).is_none());
    }
    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    k.add_inductive_checked(block("KR1Lc", Expr::prop(), vec![("KR1Lc.mk", c("KR1Lc"))]))
        .expect("control: an ordinarily named block");
}

/// `Eq`, read off `with_prelude`.
fn eq_decl() -> InductiveDecl {
    Environment::with_prelude()
        .inductive_decl_of(&name("Eq"))
        .expect("with_prelude declares Eq")
}

/// `add_quot_checked` needs `Eq` admitted THROUGH the entry: an `Eq` that
/// came in `new`'s base (present, walked, the right shape, so the kernel's
/// own `add_quot` would accept it) is refused; and asking twice is refused
/// (the kernel's `add_quot` is idempotent and would answer `Ok`). Controls:
/// `Eq` admitted through `add_inductive_checked` then `add_quot_checked`
/// installs the primitives, and the empty entry refuses for want of `Eq`.
#[test]
fn test_quotients_need_eq_admitted_through_the_entry() {
    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    let err = k
        .add_quot_checked()
        .expect_err("no Eq in the entry: the quotient primitives refuse");
    assert!(matches!(err, ReferenceRefusal::Admission(_)), "{err:?}");
    assert!(!k.environment().quot_installed());

    let mut base = Environment::default();
    base.add_inductive_core(eq_decl())
        .expect("Eq in a plain base");
    base.check_eq_for_quot()
        .expect("the base's Eq has the shape add_quot needs");
    let mut k = ReferenceKernel::new(base).expect("a base holding Eq");
    let err = k
        .add_quot_checked()
        .expect_err("an Eq handed in by the base was not admitted through the entry");
    assert!(matches!(err, ReferenceRefusal::Admission(_)), "{err:?}");
    assert!(!k.environment().quot_installed());

    let mut k = ReferenceKernel::new(Environment::default()).expect("empty base");
    k.add_inductive_checked(eq_decl())
        .expect("Eq through the entry");
    k.add_quot_checked()
        .expect("control: Eq admitted through the entry");
    assert!(k.environment().quot_installed());
    let err = k
        .add_quot_checked()
        .expect_err("the primitives are already installed");
    assert!(matches!(err, ReferenceRefusal::Admission(_)), "{err:?}");
}
