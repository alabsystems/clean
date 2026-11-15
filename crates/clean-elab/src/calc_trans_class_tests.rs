// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for RC-R: `calc` composes adjacent steps by SYNTHESIZING a
//! `Trans` instance — Lean's `Lean.Elab.Term.mkCalcTrans` — rather than looking
//! the relation pair up in a closed enum + 20-entry lemma-name table.
//!
//! # What discriminates these tests
//!
//! Every relation below is outside the seven `CalcRel` variants AND its
//! transitivity is reachable ONLY through a registered `Trans` instance:
//!
//! * the composing lemma is named `myr_compose`, never `<R>.trans`, so the
//!   relation-native `R.trans` route in `mk_calc_trans` cannot find it;
//! * the heterogeneous case composes `MyR` with `MyS` into a THIRD relation
//!   `MyT`. No same-head route and no entry of the name table can produce that
//!   — only an instance whose `outParam` output relation DETERMINES `MyT`;
//! * the instances are value-less `Declaration::Axiom`s spelled at Lean's six
//!   universes, exactly as an imported `.olean` instance reaches Clean. A
//!   version written against Clean's own reducible instances would pass with or
//!   without the mechanism, because the elaborator can unfold its way around it.
//!
//! Every test drives the full parse -> elaborate -> register pipeline, so an
//! `Ok` means the trusted kernel accepted the composed proof term.

use clean_kernel::env::{KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY};
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use clean_parser::parse_decl;

use crate::elaborate_decl_and_register;

/// Lean's six universe arguments for `Prop`-valued relations on a `Prop`
/// carrier: the three RELATION sorts are `Prop` (`Sort 0`) and the three
/// CARRIER sorts are `Sort 1` (because `Prop : Sort 1`).
fn prop_carrier_trans_levels() -> Vec<Level> {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    vec![
        zero.clone(),
        zero.clone(),
        zero,
        one.clone(),
        one.clone(),
        one,
    ]
}

/// Register `name : Trans r s t` as a value-less axiom AND as an instance of
/// the `Trans` class, the way `.olean` import surfaces an imported instance.
fn register_trans_instance(env: &mut Environment, name: &str, r: &str, s: &str, t: &str) {
    let rel = |n: &str| Expr::const_(Name::from_string(n), vec![]);
    register_trans_instance_expr(env, name, rel(r), rel(s), rel(t));
}

/// As [`register_trans_instance`], but the three relations are supplied as
/// arbitrary expressions — so a test can spell the OUTPUT relation the way an
/// imported instance actually spells it (a lambda, not a constant).
fn register_trans_instance_expr(env: &mut Environment, name: &str, r: Expr, s: Expr, t: Expr) {
    let prop = Expr::sort(Level::zero());
    let inst_type = Expr::apps(
        Expr::const_(Name::from_string("Trans"), prop_carrier_trans_levels()),
        [prop.clone(), prop.clone(), prop, r, s, t],
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: inst_type.clone(),
    })
    .expect("a `Trans` instance spelled at Lean's six universes must register");
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string(name),
        class_name: Name::from_string("Trans"),
        priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
        type_: Some(inst_type),
        value: None,
    });
}

/// Three relations on `Prop` with NO `.trans`-named lemma anywhere, plus the
/// homogeneous `Trans MyR MyR MyR` and the heterogeneous `Trans MyR MyS MyT`.
fn env_with_trans_instances() -> Environment {
    let mut env = Environment::with_prelude();
    for src in [
        "axiom MyR : Prop → Prop → Prop",
        "axiom MyS : Prop → Prop → Prop",
        "axiom MyT : Prop → Prop → Prop",
    ] {
        let decl = parse_decl(src).expect("relation scaffold should parse");
        elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|e| panic!("relation scaffold should register: {src}: {e:?}"));
    }
    register_trans_instance(&mut env, "instTransMyR", "MyR", "MyR", "MyR");
    register_trans_instance(&mut env, "instTransMyRS", "MyR", "MyS", "MyT");
    env
}

/// A relation that is a `def` whose unfolding is a `Pi` — the shape of
/// `List.Subset` (`fun l₁ l₂ => ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂`), which is the single
/// most frequent relation outside Clean's closed seven across Mathlib's `calc`
/// blocks.
///
/// `out_param_unfolded` selects how the instance spells its OUTPUT relation:
/// `false` uses the constant `MySub`, `true` uses `MySub`'s own VALUE (the
/// lambda), which is how a real imported instance's out-param arrives.
fn env_with_def_shaped_relation(out_param_unfolded: bool) -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl("def MySub (a b : Prop) : Prop := a → b")
        .expect("def-shaped relation should parse");
    elaborate_decl_and_register(&mut env, &decl).expect("def-shaped relation should register");
    let mysub = Expr::const_(Name::from_string("MySub"), vec![]);
    let out = if out_param_unfolded {
        env.get_const(&Name::from_string("MySub"))
            .and_then(|c| c.value.clone())
            .expect("`MySub` is a definition, so it has a value")
    } else {
        mysub.clone()
    };
    register_trans_instance_expr(&mut env, "instTransMySub", mysub.clone(), mysub, out);
    env
}

/// RC-R core: a two-step `calc` over a relation whose transitivity exists ONLY
/// as a `Trans` instance — no `MyR.trans` constant, no table entry — must
/// compose and kernel-check.
#[test]
fn test_calc_composes_through_a_synthesized_trans_instance() {
    let mut env = env_with_trans_instances();
    let src = "theorem t (a b c : Prop) (h1 : MyR a b) (h2 : MyR b c) : MyR a c := by \
               calc MyR a b := h1\n    MyR _ c := h2";
    let decl = parse_decl(src).expect("trans-instance calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("a calc chain whose only transitivity is a `Trans` instance must kernel-check");
}

/// The `outParam` test. `Trans MyR MyS MyT` composes two DIFFERENT relations
/// into a THIRD one. Neither the same-head `R.trans` route nor any entry of the
/// closed name table can produce `MyT` — only instance synthesis in which the
/// class's `outParam` third argument is DETERMINED by the resolved instance.
#[test]
fn test_calc_out_param_determines_the_composed_relation() {
    let mut env = env_with_trans_instances();
    let src = "theorem t (a b c : Prop) (h1 : MyR a b) (h2 : MyS b c) : MyT a c := by \
               calc MyR a b := h1\n    MyS _ c := h2";
    let decl = parse_decl(src).expect("heterogeneous trans-instance calc should parse");
    elaborate_decl_and_register(&mut env, &decl).expect(
        "the resolved `Trans` instance's out-param must determine the composed relation `MyT`",
    );
}

/// The same mechanism reached directly, with no `calc` in the picture, so a
/// failure here localizes to instance synthesis rather than to calc plumbing.
#[test]
fn test_trans_trans_term_composes_heterogeneous_instance() {
    let mut env = env_with_trans_instances();
    let src = "theorem t (a b c : Prop) (h1 : MyR a b) (h2 : MyS b c) : MyT a c := \
               Trans.trans h1 h2";
    let decl = parse_decl(src).expect("direct Trans.trans term should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("`Trans.trans h1 h2` must compose over the heterogeneous instance");
}

/// FAIL-CLOSED decoy: the instance says `MyR` then `MyS` yields `MyT`, so a
/// theorem claiming it yields `MyR` must be REJECTED. This discriminates a real
/// out-param resolution from "assume the output is the left relation".
#[test]
fn test_calc_wrong_output_relation_is_rejected() {
    let mut env = env_with_trans_instances();
    let src = "theorem t (a b c : Prop) (h1 : MyR a b) (h2 : MyS b c) : MyR a c := by \
               calc MyR a b := h1\n    MyS _ c := h2";
    let decl = parse_decl(src).expect("wrong-output calc should parse");
    assert!(
        elaborate_decl_and_register(&mut env, &decl).is_err(),
        "the composed relation is fixed by the instance's out-param; claiming a \
         different one must be REJECTED"
    );
}

/// FAIL-CLOSED decoy: the reversed pair `MyS` then `MyR` has NO instance, so
/// the chain must be rejected rather than composed from the instance that
/// happens to mention both relations.
#[test]
fn test_calc_unregistered_relation_pair_is_rejected() {
    let mut env = env_with_trans_instances();
    let src = "theorem t (a b c : Prop) (h1 : MyS a b) (h2 : MyR b c) : MyT a c := by \
               calc MyS a b := h1\n    MyR _ c := h2";
    let decl = parse_decl(src).expect("reversed-pair calc should parse");
    assert!(
        elaborate_decl_and_register(&mut env, &decl).is_err(),
        "a relation pair with no `Trans` instance must be REJECTED"
    );
}

/// FAIL-CLOSED decoy: a broken chain (middle terms do not connect) must still
/// be rejected even though a `Trans` instance for the pair exists.
#[test]
fn test_calc_broken_chain_with_instance_available_is_rejected() {
    let mut env = env_with_trans_instances();
    let src = "theorem t (a b c d : Prop) (h1 : MyR a b) (h2 : MyR c d) : MyR a d := by \
               calc MyR a b := h1\n    MyR c d := h2";
    let decl = parse_decl(src).expect("broken chain should parse");
    assert!(
        elaborate_decl_and_register(&mut env, &decl).is_err(),
        "a calc chain whose middle terms do not connect must be REJECTED"
    );
}

/// The `List.Subset` family, reproduced synthetically. `MySub` is a `def` whose
/// unfolding is a `Pi`, so composing it through `Trans.trans` used to pose the
/// constraint `?r ?a ?b =?= @MySub a b`, which is outside the Miller fragment;
/// structural dispatch then whnf-UNFOLDED `MySub a b` into `a → b` and the
/// unification failed. Lean never poses that constraint — `mkCalcTrans` supplies
/// `r`, `a`, `b` positionally from `getCalcRelation?`.
///
/// RED before the fix, with `TypeMismatch { expected: "?r ?a ?b", … }`.
#[test]
fn test_calc_over_a_def_shaped_relation_whose_unfolding_is_a_pi() {
    let mut env = env_with_def_shaped_relation(false);
    let src = "theorem t (a b c : Prop) (h1 : MySub a b) (h2 : MySub b c) : MySub a c := by \
               calc MySub a b := h1\n    MySub _ c := h2";
    let decl = parse_decl(src).expect("def-shaped relation calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("a relation whose unfolding is a `Pi` must still compose through `Trans`");
}

/// The same relation, with the instance's `outParam` output spelled the way an
/// imported instance actually spells it: `MySub`'s VALUE (a lambda whose body is
/// a `Pi`), not the constant. `Trans.trans`'s conclusion `t a c` is then a
/// beta-redex whose reduction is a `Pi`, so head-beta alone DESTROYS the
/// relation application and the "step result is not a relation" check rejects a
/// perfectly good proof. Measured under real `import Init` on
/// `Trans (@List.Sublist α) List.Subset List.Subset`.
///
/// RED before the fix, with
/// `NotImplemented("calc: composed step result is not a relation: Pi(…)")`.
#[test]
fn test_calc_out_param_arriving_unfolded_still_decomposes() {
    let mut env = env_with_def_shaped_relation(true);
    let src = "theorem t (a b c : Prop) (h1 : MySub a b) (h2 : MySub b c) : MySub a c := by \
               calc MySub a b := h1\n    MySub _ c := h2";
    let decl = parse_decl(src).expect("unfolded-out-param calc should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("an out-param that arrives as a lambda must still yield a decomposable relation");
}

/// FAIL-CLOSED companion to the two tests above: the same environment must still
/// reject a chain whose middle terms do not connect.
#[test]
fn test_calc_def_shaped_relation_broken_chain_is_rejected() {
    let mut env = env_with_def_shaped_relation(true);
    let src = "theorem t (a b c d : Prop) (h1 : MySub a b) (h2 : MySub c d) : MySub a d := by \
               calc MySub a b := h1\n    MySub c d := h2";
    let decl = parse_decl(src).expect("broken def-shaped chain should parse");
    assert!(
        elaborate_decl_and_register(&mut env, &decl).is_err(),
        "a broken chain must be REJECTED even when the relation pair has an instance"
    );
}

/// The dedicated seven-relation fallback must survive for an environment that
/// registers no `Trans` instance for the pair at all — Clean's bare kernel
/// prelude, i.e. a file checked with no `import`.
#[test]
fn test_bare_prelude_le_chain_still_kernel_checks() {
    let mut env = Environment::with_prelude();
    let src = "theorem t (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by \
               calc a ≤ b := h1\n    _ ≤ c := h2";
    let decl = parse_decl(src).expect("le chain should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("the dedicated `≤` fallback must survive on the bare prelude");
}

/// Same, for `Eq`.
#[test]
fn test_bare_prelude_eq_chain_still_kernel_checks() {
    let mut env = Environment::with_prelude();
    let src = "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by \
               calc a = b := h1\n    _ = c := h2";
    let decl = parse_decl(src).expect("eq chain should parse");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("the dedicated `=` fallback must survive on the bare prelude");
}
