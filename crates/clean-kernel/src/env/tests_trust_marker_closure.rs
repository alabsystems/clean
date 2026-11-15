// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A declaration uses sorry iff `sorryAx` / `sorry` is in its CONSTANT
//! CLOSURE — [`DomainAxiomClosure::trust_markers_of_name`], the one source of
//! every checker's "uses sorry" verdict since 2026-09-28.
//!
//! Every declaration here is admitted by the kernel's full `add_decl` check,
//! over the real prelude. The "through" cases are exactly the ones a scan of
//! the declaration's OWN terms cannot see: the declaration mentions no marker,
//! a constant it cites does.

use super::axiom_audit::{is_sorry_marker, DomainAxiomClosure};
use super::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::Declaration;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn bool_ty() -> Expr {
    c("Bool")
}

/// `(fun b : Bool => b) true` — a flag that is not a literal.
fn opaque_flag() -> Expr {
    Expr::app(
        Expr::lam(BinderInfo::Default, bool_ty(), Expr::bvar(0)),
        c("Bool.true"),
    )
}

fn marker_at(name: &str, level: Level) -> Expr {
    Expr::const_(n(name), vec![level])
}

/// The default prelude carries no trust markers (bcacce6e0); a fixture that
/// cites one opts in to the admission fragment, as a frontend does.
fn marker_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_admission_stub_theory()
        .expect("explicit admission theory for this marker fixture");
    env
}

fn def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("kernel must admit def {name}: {e:?}"));
}

fn thm(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    env.add_decl(Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: ty,
        value,
    })
    .unwrap_or_else(|e| panic!("kernel must admit theorem {name}: {e:?}"));
}

fn markers(env: &Environment, name: &str) -> Vec<String> {
    DomainAxiomClosure::new()
        .trust_markers_of_name(env, &n(name))
        .iter()
        .map(ToString::to_string)
        .collect()
}

fn own_terms_show_sorry(env: &Environment, name: &str) -> bool {
    env.get_const(&n(name))
        .expect("declared")
        .trust_summary()
        .has_sorry()
}

#[test]
fn a_non_literal_flag_is_in_the_closure_and_in_the_own_terms() {
    let mut env = marker_env();
    // theorem bad : False := @sorryAx False ((fun b => b) true)
    thm(
        &mut env,
        "bad",
        c("False"),
        Expr::apps(
            marker_at("sorryAx", Level::zero()),
            [c("False"), opaque_flag()],
        ),
    );
    assert_eq!(markers(&env, "bad"), vec!["sorryAx"]);
    assert!(
        own_terms_show_sorry(&env, "bad"),
        "the own-terms scan sees any occurrence, whatever the flag"
    );
}

#[test]
fn a_definition_alias_carries_sorry_to_its_user() {
    let mut env = marker_env();
    // def pick : Bool → False := @sorryAx False      (partially applied)
    def(
        &mut env,
        "pick",
        Expr::arrow(bool_ty(), c("False")),
        Expr::app(marker_at("sorryAx", Level::zero()), c("False")),
    );
    // theorem bad : False := pick true               (mentions no marker)
    thm(
        &mut env,
        "bad",
        c("False"),
        Expr::app(c("pick"), c("Bool.true")),
    );
    assert!(
        !own_terms_show_sorry(&env, "bad"),
        "setup: bad's own terms are clean"
    );
    assert_eq!(markers(&env, "bad"), vec!["sorryAx"]);
    assert_eq!(markers(&env, "pick"), vec!["sorryAx"]);
}

#[test]
fn a_theorem_that_only_cites_a_sorryd_lemma_uses_sorry() {
    let mut env = marker_env();
    thm(
        &mut env,
        "lemma1",
        c("False"),
        Expr::apps(
            marker_at("sorryAx", Level::zero()),
            [c("False"), c("Bool.false")],
        ),
    );
    // theorem uses : False := lemma1 ; theorem uses2 : False := uses
    thm(&mut env, "uses", c("False"), c("lemma1"));
    thm(&mut env, "uses2", c("False"), c("uses"));
    assert_eq!(markers(&env, "uses"), vec!["sorryAx"]);
    assert_eq!(
        markers(&env, "uses2"),
        vec!["sorryAx"],
        "transitively, two hops"
    );
}

#[test]
fn a_sorry_in_a_cited_type_is_in_the_closure() {
    let mut env = marker_env();
    // def T : Prop := @sorryAx Prop ((fun b => b) true)
    def(
        &mut env,
        "T",
        Expr::prop(),
        Expr::apps(
            marker_at("sorryAx", Level::succ(Level::zero())),
            [Expr::prop(), opaque_flag()],
        ),
    );
    // theorem t : T → T := fun h => h     (T only in the TYPE)
    let t_to_t = Expr::arrow(c("T"), c("T"));
    thm(
        &mut env,
        "t",
        t_to_t,
        Expr::lam(BinderInfo::Default, c("T"), Expr::bvar(0)),
    );
    assert_eq!(markers(&env, "t"), vec!["sorryAx"]);
}

#[test]
fn solver_markers_are_reached_through_an_alias_too() {
    let mut env = marker_env();
    def(
        &mut env,
        "oracle",
        c("False"),
        Expr::app(marker_at("trustedAy", Level::zero()), c("False")),
    );
    thm(&mut env, "bad", c("False"), c("oracle"));
    assert_eq!(markers(&env, "bad"), vec!["trustedAy"]);
    let mut summary = env.get_const(&n("bad")).expect("declared").trust_summary();
    assert!(summary.is_fully_verified(), "setup: own terms are clean");
    let closure = DomainAxiomClosure::new().trust_markers_of_name(&env, &n("bad"));
    assert!(summary.absorb_closure_markers(closure.iter()));
    assert_eq!(summary.trusted_ay_count, 1);
    assert!(!summary.is_fully_verified());
}

#[test]
fn a_user_axiom_is_a_disclosed_domain_axiom_not_a_sorry() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: n("bogus"),
        level_params: vec![],
        type_: c("False"),
    })
    .expect("axiom");
    thm(&mut env, "t", c("False"), c("bogus"));
    let mut closure = DomainAxiomClosure::new();
    assert!(
        closure.trust_markers_of_name(&env, &n("t")).is_empty(),
        "a user axiom is not a sorry"
    );
    let domain: Vec<String> = closure
        .of_name(&env, &n("t"))
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        domain,
        vec!["bogus"],
        "…and it IS disclosed as an assumption"
    );
}

#[test]
fn a_clean_theorem_reaches_no_marker() {
    let mut env = Environment::with_prelude();
    thm(&mut env, "t", c("True"), c("True.intro"));
    assert!(markers(&env, "t").is_empty());
}

/// Every environment a `clean check` run starts from must reach no trust
/// marker: otherwise every declaration citing the offending constant would
/// read as sorry-tainted through it. Pinned so an edit that introduces one
/// fails here, by name, instead of as a wall of spurious "uses sorry".
///
/// Covers the builtin prelude plus the registrars `clean check` adds to it
/// (`init_monad_list_insts`, `init_io_ops`, `init_ulift`), and the import
/// prelude it uses with `.olean` imports.
#[test]
fn no_check_environment_reaches_a_trust_marker() {
    fn tainted(env: &Environment) -> Vec<String> {
        let mut closure = DomainAxiomClosure::new();
        let names: Vec<Name> = env.constants().map(|info| info.name.clone()).collect();
        let mut out = Vec::new();
        for name in &names {
            if super::is_trust_marker(name) {
                continue;
            }
            let reached = closure.trust_markers_of_name(env, name);
            if !reached.is_empty() {
                out.push(format!("{name} -> {reached:?}"));
            }
        }
        out
    }
    let mut builtin = Environment::with_prelude();
    builtin
        .init_monad_list_insts()
        .expect("List monad instances");
    builtin.init_io_ops().expect("IO operations");
    builtin.init_ulift().expect("ULift");
    let import = Environment::try_with_prelude_for_import().expect("import prelude");
    for (label, env) in [
        ("builtin + registrars", &builtin),
        ("import prelude", &import),
    ] {
        let found = tainted(env);
        assert!(
            found.is_empty(),
            "{label}: {} constant(s) reach a trust marker: {:?}",
            found.len(),
            found.iter().take(20).collect::<Vec<_>>()
        );
    }
}

/// A closure that reached an ABSENT constant is answered but never memoised:
/// once the constant is declared (with a sorry in it), the same memo must see
/// it. A memo that cached "absent = clean" would answer "clean" forever.
#[test]
fn an_absent_constant_is_not_memoised_as_clean() {
    let mut env = marker_env();
    let mut closure = DomainAxiomClosure::new();
    let citing = Expr::app(c("ghost"), c("Bool.true"));
    assert!(closure.trust_markers_of_expr(&env, &citing).is_empty());
    def(
        &mut env,
        "ghost",
        Expr::arrow(bool_ty(), c("False")),
        Expr::app(marker_at("sorryAx", Level::zero()), c("False")),
    );
    let after: Vec<String> = closure
        .trust_markers_of_expr(&env, &citing)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(after, vec!["sorryAx"]);
}

#[test]
fn is_sorry_marker_is_the_sorry_half_of_the_trust_markers() {
    assert!(is_sorry_marker(&n("sorryAx")));
    assert!(is_sorry_marker(&n("sorry")));
    assert!(!is_sorry_marker(&n("trustedAy")));
    assert!(!is_sorry_marker(&n("trustedArith")));
    assert!(!is_sorry_marker(&n("sorryAxLemma")));
}
