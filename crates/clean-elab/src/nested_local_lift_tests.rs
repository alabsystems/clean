// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the nested-local lift retry (rung 2 of
//! `designs/2026-07-29-rocq-features-into-clean.md`): inductives whose nested
//! occurrences capture constructor-locals — rejected by Lean 4 with "nested
//! inductive datatypes parameters cannot contain local variables", accepted
//! by Rocq — elaborate under `set_option clean.inductive.liftNestedLocals
//! true` via specialization into kernel-re-checked aux mutual families.
//!
//! These go through the FULL surface pipeline (`elaborate_decl_and_register`,
//! the same one `clean check` uses). Sources are self-contained (no prelude
//! types) so the tests pin the lift, not the prelude.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code`, panicking on the first failure.
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

/// The minimized capturing nested inductive (shared by the on/off tests),
/// WITHOUT the option line: `Bad`'s `Wrap` occurrence captures the local `n`.
const CAPTURING_WRAP_SRC: &str = r#"
inductive Base : Type
  | o : Base

inductive Wrap (P : Base → Prop) : Prop
  | mk : P Base.o → Wrap P

inductive Bad : Base → Prop
  | step : (n : Base) → Wrap (fun (m : Base) => Bad n) → Bad n
"#;

#[test]
fn test_nested_local_lift_default_off_still_rejects() {
    let mut env = Environment::with_prelude();
    let decls = parse_file(CAPTURING_WRAP_SRC).expect("should parse");
    let mut results = Vec::new();
    for decl in &decls {
        results.push(elaborate_decl_and_register(&mut env, decl));
    }
    let (last, prefix) = results.split_last().expect("three declarations");
    for (i, r) in prefix.iter().enumerate() {
        assert!(r.is_ok(), "decl {i} must elaborate: {r:?}");
    }
    let err = last
        .as_ref()
        .expect_err("without the option the capture must fail closed");
    assert!(
        format!("{err:?}").contains("local variables"),
        "the original kernel rejection must surface, got: {err:?}"
    );
}

#[test]
fn test_nested_local_lift_option_accepts_minimized_wrap() {
    let src = format!("set_option clean.inductive.liftNestedLocals true\n{CAPTURING_WRAP_SRC}");
    let env = elab_all(&src);
    let bad = env
        .get_inductive(&Name::from_string("Bad"))
        .expect("Bad must register under the lift option");
    assert_eq!(
        bad.all_names.len(),
        2,
        "Bad is mutual with the lifted aux family"
    );
    assert!(
        env.get_inductive(&Name::from_string("_lifted.Wrap_1"))
            .is_some(),
        "the specialized family must register as a real inductive"
    );
}

#[test]
fn test_nested_local_lift_scoped_option_form() {
    // `set_option ... in <decl>` scopes the lift to one declaration.
    let src = r#"
inductive Base : Type
  | o : Base

inductive Wrap (P : Base → Prop) : Prop
  | mk : P Base.o → Wrap P

set_option clean.inductive.liftNestedLocals true in
inductive Bad : Base → Prop
  | step : (n : Base) → Wrap (fun (m : Base) => Bad n) → Bad n
"#;
    let env = elab_all(src);
    assert!(
        env.get_inductive(&Name::from_string("Bad")).is_some(),
        "scoped option form must enable the lift for the wrapped decl"
    );
}

#[test]
fn test_nested_local_lift_forall2_and_flagship() {
    // The Rocq-post flagship shape (`Forall₂` + `∧` under a lambda), fully
    // self-contained: the `Forall2` occurrence captures the ctor-local `l`
    // (round 1), and the `MyAnd` capture only materializes inside the lifted
    // family's constructor after parameter substitution + beta (round 2).
    let src = r#"
set_option clean.inductive.liftNestedLocals true

inductive SchemaTy : Type
  | leaf : SchemaTy

inductive JsonVal : Type
  | leaf : JsonVal

inductive ListP : Type
  | nil : ListP
  | cons : SchemaTy → ListP → ListP

inductive MyAnd (a : Prop) (b : Prop) : Prop
  | intro : a → b → MyAnd a b

inductive Forall2 (R : SchemaTy → JsonVal → Prop) : ListP → ListP → Prop
  | nil : Forall2 R ListP.nil ListP.nil
  | cons : (s : SchemaTy) → (j : JsonVal) → (rest : ListP) → R s j → Forall2 R rest rest → Forall2 R (ListP.cons s rest) (ListP.cons s rest)

inductive Valid : SchemaTy → JsonVal → Prop
  | ok : (s : SchemaTy) → (j : JsonVal) → Valid s j

inductive ValidCombined : ListP → Prop
  | mk : (l : ListP) → Forall2 (fun (s : SchemaTy) (j : JsonVal) => MyAnd (Valid s j) (ValidCombined l)) l l → ValidCombined l
"#;
    let env = elab_all(src);
    let vc = env
        .get_inductive(&Name::from_string("ValidCombined"))
        .expect("the Forall2-with-And declaration must register under the lift");
    assert_eq!(
        vc.all_names.len(),
        3,
        "ValidCombined is mutual with the two lifted families (rounds 1 and 2)"
    );
    assert!(
        env.get_inductive(&Name::from_string("_lifted.Forall2_1"))
            .is_some(),
        "round 1 must lift the capturing Forall2 occurrence"
    );
    assert!(
        env.get_inductive(&Name::from_string("_lifted.MyAnd_2"))
            .is_some(),
        "round 2 must lift the MyAnd capture surfaced by beta inside the aux ctor"
    );
}

#[test]
fn test_nested_local_lift_bridges_land_e2e() {
    // Rung P3: the retry also registers kernel-checked bridge lemmas back to
    // the user's original vocabulary.
    let src = format!("set_option clean.inductive.liftNestedLocals true\n{CAPTURING_WRAP_SRC}");
    let env = elab_all(&src);
    for suffix in ["bridge_mp", "bridge_mpr", "bridge"] {
        let name = Name::from_string(&format!("_lifted.Wrap_1.{suffix}"));
        assert!(
            env.get_const(&name).is_some(),
            "{name} must be registered by the retry"
        );
    }
}

#[test]
fn test_nested_local_lift_flagship_bridges_land_e2e() {
    // The Forall2+MyAnd flagship: both lifted families get their bridges,
    // with the cross-family mpr transport in play.
    let src = r#"
set_option clean.inductive.liftNestedLocals true

inductive SchemaTy : Type
  | leaf : SchemaTy

inductive JsonVal : Type
  | leaf : JsonVal

inductive ListP : Type
  | nil : ListP
  | cons : SchemaTy → ListP → ListP

inductive MyAnd (a : Prop) (b : Prop) : Prop
  | intro : a → b → MyAnd a b

inductive Forall2 (R : SchemaTy → JsonVal → Prop) : ListP → ListP → Prop
  | nil : Forall2 R ListP.nil ListP.nil
  | cons : (s : SchemaTy) → (j : JsonVal) → (rest : ListP) → R s j → Forall2 R rest rest → Forall2 R (ListP.cons s rest) (ListP.cons s rest)

inductive Valid : SchemaTy → JsonVal → Prop
  | ok : (s : SchemaTy) → (j : JsonVal) → Valid s j

inductive ValidCombined : ListP → Prop
  | mk : (l : ListP) → Forall2 (fun (s : SchemaTy) (j : JsonVal) => MyAnd (Valid s j) (ValidCombined l)) l l → ValidCombined l
"#;
    let env = elab_all(src);
    for fam in ["_lifted.Forall2_1", "_lifted.MyAnd_2"] {
        for suffix in ["bridge_mp", "bridge_mpr", "bridge"] {
            let name = Name::from_string(&format!("{fam}.{suffix}"));
            assert!(
                env.get_const(&name).is_some(),
                "{name} must be registered by the retry"
            );
        }
    }
}

#[test]
fn test_deep_induction_option_generates_principle_e2e() {
    // Rung P4: with the option on, registering a nested inductive also
    // generates the elementwise deep-induction principle + the All family.
    let src = r#"
set_option clean.inductive.deepInduction true

inductive MyTree : Type
  | node : List MyTree → MyTree
"#;
    let env = elab_all(src);
    assert!(
        env.get_inductive(&Name::from_string("List.All")).is_some(),
        "the container All family must register"
    );
    assert!(
        env.get_const(&Name::from_string("MyTree.deep_ind"))
            .is_some(),
        "MyTree.deep_ind must register"
    );
}

#[test]
fn test_deep_induction_default_off_generates_nothing() {
    let src = r#"
inductive MyTree : Type
  | node : List MyTree → MyTree
"#;
    let env = elab_all(src);
    assert!(
        env.get_const(&Name::from_string("MyTree.deep_ind"))
            .is_none(),
        "default-off must generate nothing"
    );
}

#[test]
fn test_deriving_deep_induction_marker_e2e() {
    // Explicit `deriving DeepInduction`: generates without the option.
    let src = r#"
inductive MyTree2 : Type
  | node : List MyTree2 → MyTree2
deriving DeepInduction
"#;
    let env = elab_all(src);
    assert!(
        env.get_const(&Name::from_string("MyTree2.deep_ind"))
            .is_some(),
        "deriving DeepInduction must generate the principle"
    );
}

#[test]
fn test_deriving_deep_induction_on_non_nested_is_loud() {
    // Explicit request on a non-nested type: loud error, never silent.
    let src = r#"
inductive Plain2 : Type
  | mk : Plain2
deriving DeepInduction
"#;
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).expect("should parse");
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(
        result.is_err(),
        "explicit deriving on a non-nested type must fail loudly"
    );
}
