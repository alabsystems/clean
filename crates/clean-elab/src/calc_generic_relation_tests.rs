// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for RC-R: `calc` over relations outside the dedicated
//! seven-relation table.
//!
//! Before this fix, `elab_calc_step` gated every calc step on
//! `match_goal_rel`, which recognizes only `Eq`, `Ne`, `LE.le`, `LT.lt`,
//! `GE.ge`, `GT.gt` and `Iff`. Any other relation — `List.Sublist`,
//! `List.Perm`, `Dvd.dvd`, a user's own inductive relation — was rejected up
//! front with `calc step: relation expected`, before any transitivity lemma
//! was consulted. Lean instead decomposes a step generically
//! (`Lean.Elab.Term.getCalcRelation?`: strip the last two arguments) and
//! composes through the relation's transitivity.
//!
//! Every test here drives the full `parse -> elaborate -> register` pipeline,
//! so an `Ok` means the composed proof term was accepted by the trusted
//! kernel (`register_elab_result` -> `add_decl_with_kernel_check`), not merely
//! elaborated.

use clean_kernel::Environment;
use clean_parser::parse_decl;

use crate::elaborate_decl_and_register;

/// Build an environment carrying a user relation `MyRel` on `Prop` together
/// with its own transitivity lemma `MyRel.trans`, plus an `Eq`-bearing
/// prelude. `MyRel` is deliberately NOT one of the seven relations
/// `match_goal_rel` knows.
fn env_with_user_relation() -> Environment {
    let mut env = Environment::with_prelude();
    for src in [
        "axiom MyRel : Prop → Prop → Prop",
        "axiom MyRel.trans : {a : Prop} → {b : Prop} → {c : Prop} → MyRel a b → MyRel b c → MyRel a c",
    ] {
        let decl = parse_decl(src).expect("relation scaffold should parse");
        elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|e| panic!("relation scaffold should register: {src}: {e:?}"));
    }
    env
}

/// RC-R core: a two-step `calc` over a relation the dedicated table does not
/// know must compose through the relation's own `.trans` and kernel-check.
///
/// RED before the fix with `NotImplemented("calc step: relation expected")`.
#[test]
fn test_calc_step_accepts_relation_outside_dedicated_table() {
    let mut env = env_with_user_relation();
    let src = "theorem t (a b c : Prop) (h1 : MyRel a b) (h2 : MyRel b c) : MyRel a c := by \
               calc MyRel a b := h1\n    MyRel _ c := h2";
    let decl = parse_decl(src).expect("user-relation calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("two-step calc over a non-table relation should kernel-check");
}

/// The same chain with three steps, so the composed result of step one is
/// itself re-decomposed generically before step two is chained onto it.
#[test]
fn test_calc_three_step_chain_over_relation_outside_table() {
    let mut env = env_with_user_relation();
    let src = "theorem t (a b c d : Prop) (h1 : MyRel a b) (h2 : MyRel b c) (h3 : MyRel c d) : \
               MyRel a d := by calc MyRel a b := h1\n    MyRel _ c := h2\n    MyRel _ d := h3";
    let decl = parse_decl(src).expect("three-step user-relation calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("three-step calc over a non-table relation should kernel-check");
}

/// `Eq` followed by a relation outside the table: the equality-transport arm
/// previously required BOTH sides to be recognized relations, so `a = b`
/// followed by `MyRel b c` never reached it.
///
/// RED before the fix.
#[test]
fn test_calc_eq_then_relation_outside_table_transports() {
    let mut env = env_with_user_relation();
    let src = "theorem t (a b c : Prop) (h1 : a = b) (h2 : MyRel b c) : MyRel a c := by \
               calc a = b := h1\n    MyRel _ c := h2";
    let decl = parse_decl(src).expect("eq-then-relation calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("`=` followed by a non-table relation should kernel-check");
}

/// The mirror image: a relation outside the table followed by `Eq`.
#[test]
fn test_calc_relation_outside_table_then_eq_transports() {
    let mut env = env_with_user_relation();
    let src = "theorem t (a b c : Prop) (h1 : MyRel a b) (h2 : b = c) : MyRel a c := by \
               calc MyRel a b := h1\n    _ = c := h2";
    let decl = parse_decl(src).expect("relation-then-eq calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("a non-table relation followed by `=` should kernel-check");
}

/// FAIL-CLOSED: admitting generic relations must not admit BROKEN chains. The
/// middle terms here do not connect (`MyRel a b` then `MyRel c d`), so the
/// chain must be rejected, not silently composed.
#[test]
fn test_calc_broken_chain_over_generic_relation_is_rejected() {
    let mut env = env_with_user_relation();
    let src = "theorem t (a b c d : Prop) (h1 : MyRel a b) (h2 : MyRel c d) : MyRel a d := by \
               calc MyRel a b := h1\n    MyRel c d := h2";
    let decl = parse_decl(src).expect("broken user-relation calc should parse");
    assert!(
        elaborate_decl_and_register(&mut env, &decl).is_err(),
        "a calc chain whose middle terms do not connect must be REJECTED"
    );
}

/// FAIL-CLOSED: a generic relation with no transitivity available at all must
/// fail rather than fabricate a composition.
#[test]
fn test_calc_generic_relation_without_transitivity_is_rejected() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl("axiom NoTrans : Prop → Prop → Prop")
        .expect("relation without trans should parse");
    elaborate_decl_and_register(&mut env, &decl).expect("relation without trans should register");

    let src = "theorem t (a b c : Prop) (h1 : NoTrans a b) (h2 : NoTrans b c) : NoTrans a c := by \
               calc NoTrans a b := h1\n    NoTrans _ c := h2";
    let decl = parse_decl(src).expect("no-trans calc should parse");
    assert!(
        elaborate_decl_and_register(&mut env, &decl).is_err(),
        "a relation with no transitivity lemma or instance must be REJECTED"
    );
}

/// The dedicated seven-relation table must keep its existing routing: this
/// `≤` chain composed through `Nat.le_trans` before the change and must still
/// do so after.
#[test]
fn test_calc_dedicated_le_chain_still_kernel_checks() {
    let mut env = Environment::with_prelude();
    let src = "theorem t (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by \
               calc a ≤ b := h1\n    _ ≤ c := h2";
    let decl = parse_decl(src).expect("le chain should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("dedicated `≤` calc routing must not regress");
}

/// The dedicated `Eq` routing must likewise be unchanged.
#[test]
fn test_calc_dedicated_eq_chain_still_kernel_checks() {
    let mut env = Environment::with_prelude();
    let src = "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by \
               calc a = b := h1\n    _ = c := h2";
    let decl = parse_decl(src).expect("eq chain should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("dedicated `=` calc routing must not regress");
}

// ============================================================================
// Unit tests for the generic decomposition itself
// ============================================================================

mod decomposition {
    use crate::tactic::calc_trans_match::{
        calc_endpoints, calc_relation_head, get_calc_relation, match_goal_rel,
    };
    use clean_kernel::name::Name;
    use clean_kernel::Expr;

    /// `MyRel a b` — an application of a relation the dedicated matcher does
    /// not know.
    fn user_relation_app() -> Expr {
        let rel = Expr::const_(Name::from_string("MyRel"), vec![]);
        let a = Expr::const_(Name::from_string("A"), vec![]);
        let b = Expr::const_(Name::from_string("B"), vec![]);
        Expr::app(Expr::app(rel, a), b)
    }

    /// Pins the actual gap: the dedicated matcher rejects a user relation.
    #[test]
    fn test_match_goal_rel_rejects_relation_outside_table() {
        assert!(
            match_goal_rel(&user_relation_app()).is_none(),
            "the dedicated matcher is expected to reject a non-table relation"
        );
    }

    /// Lean's `getCalcRelation?`: strip the last two arguments, whatever the
    /// head is.
    #[test]
    fn test_get_calc_relation_decomposes_relation_outside_table() {
        let (rel, lhs, rhs) = get_calc_relation(&user_relation_app())
            .expect("a two-argument application should decompose");
        assert!(
            format!("{rel:?}").contains("MyRel"),
            "relation should be the MyRel head, got {rel:?}"
        );
        assert!(format!("{lhs:?}").contains('A'), "lhs should be A");
        assert!(format!("{rhs:?}").contains('B'), "rhs should be B");
    }

    /// `calc_endpoints` must agree with the dedicated matcher wherever the
    /// latter applies, so the existing relations keep their endpoints.
    #[test]
    fn test_calc_endpoints_agrees_with_dedicated_matcher_on_eq() {
        let eq = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![]),
                    Expr::const_(Name::from_string("T"), vec![]),
                ),
                Expr::const_(Name::from_string("A"), vec![]),
            ),
            Expr::const_(Name::from_string("B"), vec![]),
        );
        let (lhs, rhs) = calc_endpoints(&eq).expect("Eq should decompose");
        let (_, _, dedicated_lhs, dedicated_rhs, _) =
            match_goal_rel(&eq).expect("Eq is a dedicated relation");
        assert_eq!(format!("{lhs:?}"), format!("{dedicated_lhs:?}"));
        assert_eq!(format!("{rhs:?}"), format!("{dedicated_rhs:?}"));
    }

    /// Fewer than two arguments is not a relation — the generic rule must not
    /// invent endpoints.
    #[test]
    fn test_get_calc_relation_rejects_under_applied_head() {
        let one_arg = Expr::app(
            Expr::const_(Name::from_string("MyRel"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        );
        assert!(
            get_calc_relation(&one_arg).is_none(),
            "a one-argument application must not decompose as a relation"
        );
        assert!(
            get_calc_relation(&Expr::const_(Name::from_string("MyRel"), vec![])).is_none(),
            "a bare constant must not decompose as a relation"
        );
    }

    /// The relation head drives the `<R>.trans` lookup.
    #[test]
    fn test_calc_relation_head_reads_the_relation_constant() {
        let head = calc_relation_head(&user_relation_app()).expect("head should be a constant");
        assert_eq!(head.to_string(), "MyRel");
    }
}
