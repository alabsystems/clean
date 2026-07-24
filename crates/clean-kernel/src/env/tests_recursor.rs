// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for recursor, casesOn, recOn, and noConfusion generation.
//!
//! Part of #2045: inductive_recursor.rs and inductive_no_confusion.rs have
//! zero direct tests. These files generate the foundational axioms (.rec,
//! .casesOn, .recOn, .noConfusionType, .noConfusion) that every inductive
//! type depends on.

use super::test_helpers::assert_const;
use super::*;
use crate::inductive::{
    count_pi_args, Constructor, InductiveDecl, InductiveType, RecursorArgOrder,
};
use crate::tc::TypeChecker;

// ── Nat helpers ──────────────────────────────────────────────────────────

fn make_nat_env() -> Environment {
    let mut env = Environment::new();
    // Eq is needed for noConfusionType value type-checking
    env.init_eq().unwrap();
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
    env
}

// ── List helpers ─────────────────────────────────────────────────────────

fn make_list_env() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let list = Name::from_string("List");

    let list_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
    );

    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );

    let nil_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        list_a.clone(),
    );

    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        cons_body,
    );

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
    env
}

// ── Empty type (no constructors) ─────────────────────────────────────────

fn make_empty_env() -> Environment {
    let mut env = Environment::new();
    let empty = Name::from_string("Empty");

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: empty,
            type_: Expr::type_(),
            constructors: vec![],
        }],
    };
    env.add_inductive(decl).unwrap();
    env
}

// ═══════════════════════════════════════════════════════════════════════════
// AC1: Tests for build_recursor — verify .rec type and reduction rules
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_nat_rec_exists() {
    let env = make_nat_env();
    assert_const(&env, "Nat.rec");
}

#[test]
fn test_nat_rec_type_arity() {
    let env = make_nat_env();
    let rec = env.get_const(&Name::from_string("Nat.rec")).unwrap();
    // Nat.rec.{u} : (motive : Nat → Sort u) → motive zero → ((n : Nat) → motive n → motive (succ n)) → (t : Nat) → motive t
    // That's 4 Pi binders: motive, minor_zero, minor_succ, major
    let arity = count_pi_args(&rec.type_);
    assert_eq!(
        arity, 4,
        "Nat.rec should have 4 Pi args (motive + 2 minors + major)"
    );
}

#[test]
fn test_nat_rec_metadata() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();
    assert_eq!(rec.num_motives, 1);
    assert_eq!(rec.num_minors, 2, "Nat has 2 constructors, so 2 minors");
    assert_eq!(rec.rules.len(), 2, "One rule per constructor");

    // Rule 0 (zero): no recursive calls, 0 fields
    assert_eq!(rec.rules[0].num_fields, 0, "zero rule should have 0 fields");

    // Rule 1 (succ): 1 field (n : Nat), recursive
    assert_eq!(rec.rules[1].num_fields, 1, "succ rule should have 1 field");
}

#[test]
fn test_nat_rec_rule_ctors() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();

    assert_eq!(
        rec.rules[0].constructor_name,
        Name::from_string("Nat.zero"),
        "First rule should be for Nat.zero"
    );
    assert_eq!(
        rec.rules[1].constructor_name,
        Name::from_string("Nat.succ"),
        "Second rule should be for Nat.succ"
    );
}

#[test]
fn test_nat_rec_is_large_elim() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.rec")).unwrap();
    // Nat is in Type 0, not Prop, so it should have large elimination
    // Large elim means the motive universe is a fresh parameter
    assert!(
        !rec.level_params.is_empty(),
        "Nat.rec should have universe params (large elim)"
    );
}

#[test]
fn test_list_rec_exists() {
    let env = make_list_env();
    assert_const(&env, "List.rec");
}

#[test]
fn test_list_rec_metadata() {
    let env = make_list_env();
    let rec = env.get_recursor(&Name::from_string("List.rec")).unwrap();
    assert_eq!(rec.num_motives, 1);
    assert_eq!(rec.num_minors, 2, "List has 2 constructors");
    assert_eq!(rec.rules.len(), 2);

    // nil: 0 fields (param A is not counted)
    assert_eq!(rec.rules[0].num_fields, 0, "nil rule: 0 fields");

    // cons: 2 fields (head : A, tail : List A), tail is recursive
    assert_eq!(rec.rules[1].num_fields, 2, "cons rule: 2 fields");
}

#[test]
fn test_list_rec_type_arity() {
    let env = make_list_env();
    let rec = env.get_const(&Name::from_string("List.rec")).unwrap();
    // List.rec.{u,v} : {A : Type u} → (motive : List A → Sort v) →
    //   motive nil → ((head : A) → (tail : List A) → motive tail → motive (cons head tail)) →
    //   (t : List A) → motive t
    // That's: 1 param (A) + 1 motive + 2 minors + 1 major = 5
    let arity = count_pi_args(&rec.type_);
    assert_eq!(
        arity, 5,
        "List.rec: 1 param + 1 motive + 2 minors + 1 major = 5"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// AC2: Tests for build_cases_on — casesOn omits induction hypotheses
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_nat_cases_on_exists() {
    let env = make_nat_env();
    assert_const(&env, "Nat.casesOn");
}

#[test]
fn test_nat_cases_on_metadata() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.casesOn")).unwrap();
    assert_eq!(rec.num_motives, 1);
    // casesOn has same number of minors but NO induction hypotheses in them
    assert_eq!(rec.num_minors, 2, "casesOn: 2 minors for Nat");
    assert_eq!(rec.rules.len(), 2);
}

#[test]
fn test_nat_cases_on_type_arity() {
    let env = make_nat_env();
    let rec = env.get_const(&Name::from_string("Nat.casesOn")).unwrap();
    // Nat.casesOn.{u} : (motive : Nat → Sort u) → (t : Nat) →
    //   motive zero → ((n : Nat) → motive (succ n)) → motive t
    // casesOn reorders: major comes before minors
    // 1 motive + 1 major + 2 minors = 4
    let arity = count_pi_args(&rec.type_);
    assert_eq!(arity, 4, "Nat.casesOn: 1 motive + 1 major + 2 minors = 4");
}

#[test]
fn test_nat_cases_on_arg_order() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.casesOn")).unwrap();
    // Lean-faithful casesOn order: major right after the motive, before the
    // minors (same layout as recOn) — matching Lean 4's generated casesOn.
    assert_eq!(
        rec.arg_order,
        RecursorArgOrder::MajorAfterMotive,
        "casesOn should use MajorAfterMotive ordering"
    );
}

/// Regression for the GRADUATION #3 blocker (List.concat.match_1 /
/// Int.neg.match_1): the generated casesOn TYPE must spell Lean's binder
/// telescope — params → motive → (indices →) major → minors — so values
/// elaborated against Lean's casesOn (e.g. `.olean` match auxiliaries)
/// re-typecheck against a Clean-regenerated environment. The old rec-layout
/// spelling put the minors before the major, landing every Lean-order
/// application's scrutinee in the first minor slot.
#[test]
fn test_nat_cases_on_type_spells_lean_layout() {
    let env = make_nat_env();
    let cases = env.get_const(&Name::from_string("Nat.casesOn")).unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Binder 0: motive (Nat → Sort u). Binder 1: the MAJOR premise (t : Nat).
    // Binders 2-3: the zero/succ minors. Old layout had the major at the end.
    let ExprKind::Pi(_, motive_ty, rest) = &cases.type_.kind else {
        panic!("casesOn type must start with the motive Pi");
    };
    assert!(
        matches!(&motive_ty.kind, ExprKind::Pi(_, dom, _) if **dom == nat),
        "binder 0 must be the motive (Nat -> Sort u), got {motive_ty}"
    );
    let ExprKind::Pi(_, major_ty, rest) = &rest.kind else {
        panic!("casesOn type must have a second Pi binder");
    };
    assert_eq!(
        **major_ty, nat,
        "binder 1 must be the major premise (t : Nat) — Lean's casesOn \
         layout, NOT the rec layout's first minor"
    );
    let ExprKind::Pi(_, zero_minor_ty, _) = &rest.kind else {
        panic!("casesOn type must have a third Pi binder");
    };
    // The zero minor is `motive Nat.zero` — an application, not Nat.
    assert!(
        matches!(&zero_minor_ty.kind, ExprKind::App(_, _)),
        "binder 2 must be the zero minor (motive zero), got {zero_minor_ty}"
    );
}

#[test]
fn test_list_cases_on_exists() {
    let env = make_list_env();
    assert_const(&env, "List.casesOn");
}

#[test]
fn test_list_cases_on_succ_minor_no_ih() {
    let env = make_list_env();
    let rec = env
        .get_recursor(&Name::from_string("List.casesOn"))
        .unwrap();
    // cons minor in casesOn: (head : A) → (tail : List A) → motive (cons head tail)
    // NO induction hypothesis (motive tail) unlike rec
    // cons rule: 2 fields (head, tail) — same as rec
    assert_eq!(rec.rules[1].num_fields, 2, "casesOn cons: 2 fields (no IH)");
}

// ═══════════════════════════════════════════════════════════════════════════
// AC3: Tests for build_rec_on — recOn reorders major argument
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_nat_rec_on_exists() {
    let env = make_nat_env();
    assert_const(&env, "Nat.recOn");
}

#[test]
fn test_nat_rec_on_metadata() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.recOn")).unwrap();
    assert_eq!(rec.num_motives, 1);
    assert_eq!(rec.num_minors, 2);
    assert_eq!(rec.rules.len(), 2);
}

#[test]
fn test_nat_rec_on_arg_order() {
    let env = make_nat_env();
    let rec = env.get_recursor(&Name::from_string("Nat.recOn")).unwrap();
    // recOn uses MajorAfterMotive: params → motive → major → minors
    assert_eq!(
        rec.arg_order,
        RecursorArgOrder::MajorAfterMotive,
        "recOn should use MajorAfterMotive ordering"
    );
}

#[test]
fn test_nat_rec_on_type_arity() {
    let env = make_nat_env();
    let rec = env.get_const(&Name::from_string("Nat.recOn")).unwrap();
    // Same as Nat.rec but with major reordered before minors
    // motive + major + minor_zero + minor_succ = 4
    let arity = count_pi_args(&rec.type_);
    assert_eq!(arity, 4, "Nat.recOn: 1 motive + 1 major + 2 minors = 4");
}

// ═══════════════════════════════════════════════════════════════════════════
// AC4+5: Tests for noConfusionType and noConfusion
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_nat_no_confusion_type_exists() {
    let env = make_nat_env();
    // noConfusionType is a definition (constant with value), not a recursor
    let ci = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .expect("Nat.noConfusionType should exist");
    assert!(
        ci.value.is_some(),
        "noConfusionType should be a definition (has value)"
    );
}

#[test]
fn test_nat_no_confusion_exists() {
    let env = make_nat_env();
    // noConfusion is a definition (not a recursor) — reduces via delta
    let ci = env
        .get_const(&Name::from_string("Nat.noConfusion"))
        .expect("Nat.noConfusion should exist as a constant");
    assert!(
        ci.value.is_some(),
        "Nat.noConfusion should have a value (it's a definition)"
    );
    assert!(
        env.get_recursor(&Name::from_string("Nat.noConfusion"))
            .is_none(),
        "Nat.noConfusion should NOT be a recursor"
    );
}

#[test]
fn test_nat_no_confusion_type_arity() {
    let env = make_nat_env();
    let ci = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .unwrap();
    // Nat.noConfusionType.{u} : Sort u → Nat → Nat → Sort u
    // That's 3 Pi args: P, a, b
    let arity = count_pi_args(&ci.type_);
    assert_eq!(arity, 3, "Nat.noConfusionType: P + a + b = 3 args");
}

#[test]
fn test_list_no_confusion_type_exists() {
    let env = make_list_env();
    let ci = env
        .get_const(&Name::from_string("List.noConfusionType"))
        .expect("List.noConfusionType should exist");
    ci.value
        .as_ref()
        .expect("List.noConfusionType should have a definition value");
}

#[test]
fn test_list_no_confusion_arity() {
    let env = make_list_env();
    let ci = env
        .get_const(&Name::from_string("List.noConfusionType"))
        .unwrap();
    // v4.30 heterogeneous convention
    // (designs/2026-07-03-noconfusion-ctoridx-convention.md §3):
    // List.noConfusionType.{v,u} :
    //   Sort v → {A : Type u} → List A → {A' : Type u} → List A' → Sort v
    // 5 Pi args: P, A, a, A', b (P first; second major generalized over A').
    let arity = count_pi_args(&ci.type_);
    assert_eq!(
        arity, 5,
        "List.noConfusionType: P + A + a + A' + b = 5 args"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// AC6: Edge cases — Empty type, Prop-valued inductive
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_empty_type_rec_exists() {
    let env = make_empty_env();
    assert_const(&env, "Empty.rec");
}

#[test]
fn test_empty_type_rec_metadata() {
    let env = make_empty_env();
    let rec = env.get_recursor(&Name::from_string("Empty.rec")).unwrap();
    assert_eq!(
        rec.num_minors, 0,
        "Empty type has 0 constructors = 0 minors"
    );
    assert_eq!(rec.rules.len(), 0, "Empty type has 0 reduction rules");
}

#[test]
fn test_empty_type_rec_type_arity() {
    let env = make_empty_env();
    let rec = env.get_const(&Name::from_string("Empty.rec")).unwrap();
    // Empty.rec.{u} : (motive : Empty → Sort u) → (t : Empty) → motive t
    // 2 Pi args: motive, major
    let arity = count_pi_args(&rec.type_);
    assert_eq!(arity, 2, "Empty.rec: motive + major = 2 args");
}

#[test]
fn test_empty_type_cases_on_exists() {
    let env = make_empty_env();
    assert_const(&env, "Empty.casesOn");
}

#[test]
fn test_prop_singleton_large_elim() {
    // Per Lean 4 semantics: a Prop singleton with 0 constructor fields
    // (like PUnit, True) DOES allow large elimination. The recursor gets
    // an extra universe parameter enabling elimination into any type.
    // Reference: lean4/src/library/util.cpp:217 (can_elim_to_type)
    let mut env = Environment::new();
    let unit = Name::from_string("PUnit");

    // PUnit : Prop   (lives in Sort 0)
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: unit.clone(),
            type_: Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop
            constructors: vec![Constructor {
                name: Name::from_string("PUnit.unit"),
                type_: Expr::const_(unit.clone(), vec![]),
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    let ind = env.get_inductive(&Name::from_string("PUnit")).unwrap();
    assert!(
        ind.is_large_elim,
        "Prop singleton with 0 fields should have large elimination (Lean 4 semantics)"
    );
}

#[test]
fn test_prop_inductive_no_confusion_skipped() {
    // Prop-valued inductives should NOT get noConfusionType/noConfusion
    let mut env = Environment::new();
    let unit = Name::from_string("PUnit");

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: unit.clone(),
            type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
            constructors: vec![Constructor {
                name: Name::from_string("PUnit.unit"),
                type_: Expr::const_(unit.clone(), vec![]),
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    // noConfusionType should not exist for Prop types
    assert!(
        env.get_const(&Name::from_string("PUnit.noConfusionType"))
            .is_none(),
        "Prop inductive should not have noConfusionType"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// AC7 (partial): Parity check — verify generated types typecheck
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_nat_rec_type_typechecks() {
    let env = make_nat_env();
    let rec_ci = env.get_const(&Name::from_string("Nat.rec")).unwrap();
    let tc = TypeChecker::new(&env);
    // The type of the recursor should itself be well-typed
    let result = tc.infer_type(&rec_ci.type_);
    assert!(
        result.is_ok(),
        "Nat.rec type should be well-typed: {:?}",
        result.err()
    );
}

#[test]
fn test_nat_no_confusion_type_value_typechecks() {
    let env = make_nat_env();
    let ci = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .unwrap();
    let value = ci.value.as_ref().expect("should have value");
    let tc = TypeChecker::new(&env);
    // The definition body should typecheck against its declared type
    let result = tc.check_type(value, &ci.type_);
    assert!(
        result.is_ok(),
        "Nat.noConfusionType value should typecheck: {:?}",
        result.err()
    );
}

#[test]
fn test_list_rec_type_typechecks() {
    let env = make_list_env();
    let rec_ci = env.get_const(&Name::from_string("List.rec")).unwrap();
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type(&rec_ci.type_);
    assert!(
        result.is_ok(),
        "List.rec type should be well-typed: {:?}",
        result.err()
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Behavioral reduction tests — exercises actual recursor/casesOn/noConfusion
// reduction via WHNF, not just metadata/existence checks.
//
// Added per Prover audit (P1 iteration 715): all 30 original tests are
// metadata-only. These tests verify the actual computational behavior of
// generated axioms.
// ═══════════════════════════════════════════════════════════════════════════

// ── Nat.rec behavioral reduction ────────────────────────────────────────

/// Nat.rec on zero reduces to the zero_case minor.
///
/// Nat.rec (fun _ => Nat) Nat.zero (fun n ih => succ ih) Nat.zero
///   ==> Nat.zero
#[test]
fn test_nat_rec_reduction_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // motive: fun (_ : Nat) => Nat
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = zero.clone();
    // succ_case: fun (n : Nat) (ih : Nat) => Nat.succ ih
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0), // ih
            ),
        ),
    );

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())], // eliminating into Type
    );

    // Nat.rec motive zero_case succ_case Nat.zero
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), zero_case.clone()),
            succ_case,
        ),
        zero.clone(),
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, zero_case,
        "Nat.rec on zero should reduce to zero_case (Nat.zero)"
    );
}

/// Nat.rec on (succ zero) reduces correctly through the recursive step.
///
/// With identity-on-Nat recursor:
///   Nat.rec (fun _ => Nat) zero (fun n ih => succ ih) (succ zero)
///   ==> succ (Nat.rec ... zero)
///   ==> succ zero
#[test]
fn test_nat_rec_reduction_succ() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = zero.clone();
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0), // ih
            ),
        ),
    );

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    // Nat.rec motive zero_case succ_case (succ zero)
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        one.clone(),
    );

    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&result, &one),
        "Nat.rec identity on (succ zero) should reduce to (succ zero), got: {result:?}"
    );
}

/// Nat.rec on (succ (succ zero)) — verifies 2-deep recursion.
///
///   Nat.rec (fun _ => Nat) zero (fun n ih => succ ih) (succ (succ zero))
///   ==> succ (succ zero)
#[test]
fn test_nat_rec_reduction_succ_succ() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = |e: Expr| Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e);
    let two = succ(succ(zero.clone()));

    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = zero.clone();
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        two.clone(),
    );

    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&result, &two),
        "Nat.rec identity on 2 should reduce to 2, got: {result:?}"
    );
}

// ── Nat.casesOn behavioral reduction ────────────────────────────────────

/// Nat.casesOn on zero selects the zero minor.
///
///   Nat.casesOn (fun _ => Prop) Nat.zero ZeroResult (fun n => SuccResult)
///   ==> ZeroResult
#[test]
fn test_nat_cases_on_reduction_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let cases_on = Expr::const_(
        Name::from_string("Nat.casesOn"),
        vec![Level::zero()], // eliminating into Prop
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::prop());
    let zero_result = Expr::const_(Name::from_string("ZeroResult"), vec![]);
    // casesOn succ minor: fun (n : Nat) => SuccResult  (no IH)
    let succ_result = Expr::const_(Name::from_string("SuccResult"), vec![]);
    let succ_minor = Expr::lam(BinderInfo::Default, nat.clone(), succ_result);

    // Lean-faithful casesOn order: motive, major, zero_minor, succ_minor
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(cases_on, motive), zero),
            zero_result.clone(),
        ),
        succ_minor,
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, zero_result,
        "casesOn on zero should reduce to zero_result"
    );
}

/// Nat.casesOn on (succ zero) selects the succ minor and passes the
/// predecessor — without an induction hypothesis (unlike rec).
///
///   Nat.casesOn (fun _ => Prop) (succ zero) ZeroResult (fun n => Q)
///   ==> Q
#[test]
fn test_nat_cases_on_reduction_succ() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    let cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::prop());
    let zero_result = Expr::const_(Name::from_string("ZeroResult"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    // succ minor: fun (n : Nat) => Q  — casesOn does NOT pass IH
    let succ_minor = Expr::lam(BinderInfo::Default, nat.clone(), q.clone());

    // Lean-faithful casesOn order: motive, major, zero_minor, succ_minor
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(cases_on, motive), one), zero_result),
        succ_minor,
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, q,
        "casesOn on (succ zero) should reduce to Q (no IH)"
    );
}

// ── Nat.recOn behavioral reduction ──────────────────────────────────────

/// Nat.recOn on zero reduces to zero_case.
/// recOn arg order is MajorAfterMotive: motive, major, zero_case, succ_case.
#[test]
fn test_nat_rec_on_reduction_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let rec_on = Expr::const_(Name::from_string("Nat.recOn"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::prop());
    let zero_case = Expr::const_(Name::from_string("ZeroCase"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::const_(Name::from_string("SuccCase"), vec![]),
        ),
    );

    // recOn MajorAfterMotive: motive, major, zero_case, succ_case
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec_on, motive), zero),
            zero_case.clone(),
        ),
        succ_case,
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, zero_case,
        "recOn on zero should reduce to zero_case"
    );
}

// ── noConfusionType behavioral reduction ────────────────────────────────

/// noConfusionType applied to same constructor (zero/zero) reduces to (P → P).
///
///   Nat.noConfusionType Type zero zero  ==>  (Type → Type)
#[test]
fn test_no_confusion_type_reduction_same_ctor() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let nct = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())], // u = 1 (Type)
    );

    // Nat.noConfusionType Type zero zero
    let app = Expr::app(Expr::app(Expr::app(nct, Expr::type_()), zero.clone()), zero);

    let result = tc.whnf(&app);

    // Same constructor (zero/zero) with 0 fields → (P → P)
    match &result.kind {
        ExprKind::Pi(_, domain, codomain) => {
            assert!(
                matches!(&domain.as_ref().kind, ExprKind::Sort(_)),
                "Expected Sort (Type) in domain of (P → P), got: {domain:?}"
            );
            assert!(
                matches!(&codomain.as_ref().kind, ExprKind::Sort(_)),
                "Expected Sort (Type) in codomain of (P → P), got: {codomain:?}"
            );
        }
        _ => panic!("noConfusionType zero/zero should reduce to Pi (P → P), got: {result:?}"),
    }
}

/// noConfusionType applied to different constructors (zero/succ) reduces to P.
///
///   Nat.noConfusionType Type zero (succ zero)  ==>  Type
#[test]
fn test_no_confusion_type_reduction_diff_ctor() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    let nct = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );

    // Nat.noConfusionType Type zero (succ zero)
    let app = Expr::app(Expr::app(Expr::app(nct, Expr::type_()), zero), one);

    let result = tc.whnf(&app);

    // Different constructors → P (= Type)
    assert!(
        matches!(&result.kind, ExprKind::Sort(_)),
        "noConfusionType zero/(succ zero) should reduce to Sort (Type), got: {result:?}"
    );
}

/// noConfusionType with succ/succ — same constructor with 1 field
/// produces equality arrow: (Eq Nat n m → P) → P.
#[test]
fn test_no_confusion_type_reduction_succ_succ() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let nct = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );

    // Nat.noConfusionType Type (succ zero) (succ zero)
    let succ_zero = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);
    let app = Expr::app(
        Expr::app(Expr::app(nct, Expr::type_()), succ_zero.clone()),
        succ_zero,
    );

    let result = tc.whnf(&app);

    // succ/succ with 1 field → ((Eq Nat zero zero → P) → P)
    // Outer: Pi (domain = (Eq Nat zero zero → Type)) (codomain = Type)
    match &result.kind {
        ExprKind::Pi(_, domain, codomain) => {
            // codomain should be Sort (Type)
            assert!(
                matches!(&codomain.as_ref().kind, ExprKind::Sort(_)),
                "Expected Sort in outer codomain, got: {codomain:?}"
            );
            // domain should be a Pi: (Eq Nat zero zero → Type)
            match &domain.as_ref().kind {
                ExprKind::Pi(_, eq_domain, inner_codomain) => {
                    // inner codomain should be Sort
                    assert!(
                        matches!(&inner_codomain.as_ref().kind, ExprKind::Sort(_)),
                        "Expected Sort in inner codomain, got: {inner_codomain:?}"
                    );
                    // eq_domain should be an App (Eq applied to args)
                    assert!(
                        matches!(&eq_domain.as_ref().kind, ExprKind::App(..)),
                        "Expected Eq App in inner domain, got: {eq_domain:?}"
                    );
                }
                other => panic!("Expected Pi (Eq -> Sort) in outer domain, got: {other:?}"),
            }
        }
        _ => panic!("noConfusionType succ/succ should reduce to a Pi type, got: {result:?}"),
    }
}

// ── [R1] elim gate: possibly-zero result levels restrict to Prop ─────────
// design 2026-07-02-parameterized-nested-inductives.md [R1]: Lean gates the
// Prop-only-elimination restriction on `is_not_zero` (inductive.cpp:481-484),
// not on a syntactically-zero result sort. `Sort u` / `Sort (imax 1 u)`
// results CAN be zero at u := 0, so a single-ctor type with a non-Prop field
// must be Prop-only — the old syntactic gate large-eliminated it, a
// proof-irrelevance violation.

/// `Wrap.{u} (α : Sort u) : Sort (imax 1 u) | mk : α → Wrap α` — the
/// imax-generalized `Nonempty`. Result level `imax 1 u` is zero at `u := 0`,
/// and the field `α` is neither Prop-sorted nor an index ⇒ Prop-only.
#[test]
fn test_possibly_zero_sort_single_ctor_is_prop_only() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let wrap = Name::from_string("Wrap");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let result_sort = Expr::from_kind(ExprKind::Sort(Level::imax(
        Level::succ(Level::zero()),
        Level::param(u.clone()),
    )));

    // Wrap : Π (α : Sort u). Sort (imax 1 u)
    let wrap_type = Expr::pi(BinderInfo::Default, sort_u.clone(), result_sort);
    // mk : Π (α : Sort u) (a : α). Wrap α
    let mk_type = Expr::pi(
        BinderInfo::Default,
        sort_u,
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(
                Expr::const_(wrap.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: wrap.clone(),
            type_: wrap_type,
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("Wrap should be accepted");

    let val = env.inductives.get(&wrap).expect("Wrap in env");
    assert!(
        !val.is_large_elim,
        "possibly-zero result level with a non-Prop non-index field must be \
         Prop-only (Lean is_not_zero gate)"
    );
    let rec = env
        .recursors
        .get(&Name::from_string("Wrap.rec"))
        .expect("Wrap.rec should exist");
    assert_eq!(
        rec.level_params,
        vec![u],
        "Prop-only recursor must not mint a fresh elim level"
    );
}

/// Guard against over-restriction: the PUnit shape
/// `PU.{u} : Sort u | mk : PU` has no fields, so it large-eliminates even
/// though its result level is possibly zero (Lean accepts identically).
#[test]
fn test_possibly_zero_sort_no_fields_still_large_elim() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let pu = Name::from_string("PU");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    env.add_inductive(InductiveDecl {
        level_params: vec![u],
        num_params: 0,
        types: vec![InductiveType {
            name: pu.clone(),
            type_: sort_u,
            constructors: vec![Constructor {
                name: Name::from_string("PU.mk"),
                type_: Expr::const_(pu.clone(), vec![Level::param(Name::from_string("u"))]),
            }],
        }],
    })
    .expect("PU should be accepted");

    let val = env.inductives.get(&pu).expect("PU in env");
    assert!(
        val.is_large_elim,
        "a field-less possibly-zero type (PUnit shape) must keep large elimination"
    );
}
