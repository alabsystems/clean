// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness + behavior tests for Track T's two `DecidableEq` completions:
//!
//! 1. **Multi-field same-ctor decision** — `inductive Pr | mk : Nat -> Nat -> Pr
//!    deriving DecidableEq` previously dispatched to the single-constructor
//!    reflexivity shortcut (`isTrue (Eq.refl a) : a = a`), which is ill-typed for
//!    the goal `a = b` whenever the ctor carries fields (`Pr.mk 1 2 = Pr.mk 1 3`
//!    are distinct). The fix routes a single FIELDED ctor through the fielded
//!    builder so every field is decided.
//!
//! 2. **Nested-`List Self` recursion** — `tuple : List Ty -> Ty` uses a
//!    restored companion recursion (`num_motives = 2`). A dedicated mutual-`rec`
//!    builder (`decidable_eq_list_recursive.rs`) discharges it sorry-free, and a
//!    companion kernel fix makes `Ty.noConfusionType` reduce for mutual types so
//!    the `noConfusion`-based `isFalse` branches kernel-check and reduce.
//!
//! Every derived instance here is asserted to: register, infer-type against the
//! kernel, contain NO `sorry`/`sorryAx`, have EMPTY `axiom_deps`, and DECIDE
//! correctly (`if a = b then 1 else 0` reduces to the right `Nat`).

use crate::elaborate_decl_and_register;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, TypeChecker};
use clean_parser::parse_decl;

/// Register a sequence of decls into a fresh prelude env.
fn env_with(decls: &[&str]) -> Environment {
    let mut env = Environment::with_prelude();
    for d in decls {
        let decl = parse_decl(d).unwrap_or_else(|e| panic!("parse {d:?}: {e:?}"));
        elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|e| panic!("register {d:?}: {e:?}"));
    }
    env
}

/// Whether `e` references a `sorry`/`sorryAx` constant anywhere.
fn mentions_sorry(e: &Expr) -> bool {
    fn name_is_sorry(n: &Name) -> bool {
        let s = n.to_string();
        s == "sorry" || s == "sorryAx" || s.ends_with(".sorry") || s.ends_with(".sorryAx")
    }
    match e.kind() {
        ExprKind::Const(n, _) => name_is_sorry(n),
        ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => mentions_sorry(t) || mentions_sorry(b),
        _ => false,
    }
}

/// Assert the named instance is sorry-free, infer-types, and has empty deps.
fn assert_instance_sound(env: &Environment, inst_name: &str) {
    let inst = Name::from_string(inst_name);
    let info = env
        .get_const(&inst)
        .unwrap_or_else(|| panic!("{inst_name} must be registered"));
    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{inst_name} has a value"));

    assert!(
        !mentions_sorry(value),
        "{inst_name} must NOT emit sorry/sorryAx"
    );

    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("{inst_name} value must infer-type: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{inst_name} inferred type must match declared DecidableEq type"
    );

    let deps = env
        .axiom_deps(&inst)
        .unwrap_or_else(|| panic!("{inst_name} present for axiom_deps"));
    assert!(
        deps.is_empty(),
        "{inst_name} must have EMPTY axiom_deps, got {deps:?}"
    );
}

/// Evaluate `if (a_src = b_src) then 1 else 0` and WHNF to a Nat literal string.
fn pick_reduces(env: &Environment, a_src: &str, b_src: &str) -> String {
    let mut env = env.clone();
    let d = parse_decl(&format!(
        "def __pick : Nat := if ({a_src} = {b_src}) then 1 else 0"
    ))
    .expect("parse pick");
    elaborate_decl_and_register(&mut env, &d).expect("register pick");
    let pick = Expr::const_(Name::from_string("__pick"), vec![]);
    let tc = TypeChecker::new(&env);
    format!("{:?}", tc.whnf(&pick).kind())
}

fn picks_equal(env: &Environment, a: &str, b: &str) -> bool {
    pick_reduces(env, a, b).contains("Small(1)")
}

// ===================================================================
// (1) Multi-field same-ctor decision (the single-fielded-ctor bug).
// ===================================================================

#[test]
fn multifield_single_ctor_registers_sound() {
    let env = env_with(&["inductive Pr where | mk : Nat -> Nat -> Pr deriving DecidableEq"]);
    assert_instance_sound(&env, "instPrDecidableEq");
}

#[test]
fn multifield_single_ctor_decides_each_field() {
    let env = env_with(&["inductive Pr where | mk : Nat -> Nat -> Pr deriving DecidableEq"]);
    // identical ⇒ equal
    assert!(picks_equal(&env, "Pr.mk 1 2", "Pr.mk 1 2"));
    // SECOND field differs ⇒ NOT equal (the exact bug: was `a = a` ⇒ wrongly equal)
    assert!(!picks_equal(&env, "Pr.mk 1 2", "Pr.mk 1 3"));
    // FIRST field differs ⇒ NOT equal
    assert!(!picks_equal(&env, "Pr.mk 7 2", "Pr.mk 9 2"));
}

#[test]
fn multifield_three_fields_decides() {
    let env =
        env_with(&["inductive Tri where | mk : Nat -> Nat -> Nat -> Tri deriving DecidableEq"]);
    assert_instance_sound(&env, "instTriDecidableEq");
    assert!(picks_equal(&env, "Tri.mk 1 2 3", "Tri.mk 1 2 3"));
    assert!(!picks_equal(&env, "Tri.mk 9 2 3", "Tri.mk 1 2 3")); // field 0
    assert!(!picks_equal(&env, "Tri.mk 1 9 3", "Tri.mk 1 2 3")); // field 1
    assert!(!picks_equal(&env, "Tri.mk 1 2 9", "Tri.mk 1 2 3")); // field 2
}

#[test]
fn multifield_multi_ctor_still_decides() {
    // Regression: the existing >=2-ctor fielded path is unaffected.
    let env = env_with(&[
        "inductive Two where | a : Nat -> Nat -> Two | b : Nat -> Two deriving DecidableEq",
    ]);
    assert_instance_sound(&env, "instTwoDecidableEq");
    assert!(picks_equal(&env, "Two.a 1 2", "Two.a 1 2"));
    assert!(!picks_equal(&env, "Two.a 1 2", "Two.a 1 3"));
    assert!(!picks_equal(&env, "Two.a 1 2", "Two.b 1"));
    assert!(picks_equal(&env, "Two.b 5", "Two.b 5"));
}

#[test]
fn single_nullary_ctor_still_reflexive() {
    // A genuinely-trivial single NULLARY ctor (Unit-like) stays on the
    // reflexivity shortcut and decides equal.
    let env = env_with(&["inductive MyUnit where | u deriving DecidableEq"]);
    assert_instance_sound(&env, "instMyUnitDecidableEq");
    assert!(picks_equal(&env, "MyUnit.u", "MyUnit.u"));
}

// ===================================================================
// (2) Nested-`List Self` recursive DecidableEq via mutual rec.
// ===================================================================

const TY_DECL: &str =
    "inductive Ty where | int | vector : Nat -> Ty | tuple : List Ty -> Ty deriving DecidableEq";

#[test]
fn listself_registers_sound() {
    let env = env_with(&[TY_DECL]);
    assert_instance_sound(&env, "instTyDecidableEq");
}

#[test]
fn listself_decides_non_tuple_ctors() {
    let env = env_with(&[TY_DECL]);
    assert!(picks_equal(&env, "Ty.int", "Ty.int"));
    assert!(!picks_equal(&env, "Ty.int", "Ty.vector 0"));
    assert!(picks_equal(&env, "Ty.vector 3", "Ty.vector 3"));
    assert!(!picks_equal(&env, "Ty.vector 1", "Ty.vector 2"));
}

#[test]
fn listself_decides_tuple_elementwise() {
    // Restored nested constructors use the declared standard List surface.
    let env = env_with(&[TY_DECL]);
    let empty = "Ty.tuple List.nil";
    let one_int = "Ty.tuple (List.cons Ty.int List.nil)";
    let one_vec = "Ty.tuple (List.cons (Ty.vector 0) List.nil)";

    assert!(picks_equal(&env, empty, empty));
    assert!(picks_equal(&env, one_int, one_int));
    // element differs (int vs vector) ⇒ NOT equal
    assert!(!picks_equal(&env, one_int, one_vec));
    // length differs ⇒ NOT equal
    assert!(!picks_equal(&env, one_int, empty));
}

#[test]
fn listself_noconfusion_type_reduces_for_mutual() {
    // The kernel-side fix: `Ty.noConfusionType False int (vector 0)` must reduce
    // to `False` for the MUTUAL `Ty` (it previously stuck on an under-applied
    // `Ty.casesOn`, blocking every `noConfusion`-based `isFalse`).
    let env = env_with(&[TY_DECL]);
    let tc = TypeChecker::new(&env);
    let nct = Expr::const_(
        Name::from_string("Ty.noConfusionType"),
        vec![clean_kernel::Level::zero()],
    );
    let zero = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
        clean_kernel::BigNat::Small(0),
    )));
    let e = Expr::app(
        Expr::app(
            Expr::app(nct, Expr::const_(Name::from_string("False"), vec![])),
            Expr::const_(Name::from_string("Ty.int"), vec![]),
        ),
        Expr::app(Expr::const_(Name::from_string("Ty.vector"), vec![]), zero),
    );
    let w = tc.whnf(&e);
    assert!(
        matches!(w.kind(), ExprKind::Const(n, _) if n.to_string() == "False"),
        "Ty.noConfusionType (distinct ctors) must reduce to False, got {:?}",
        w.kind()
    );
}

#[test]
fn listself_sound_with_preceding_inductives() {
    // Track-relevant: even when OTHER inductives precede `Ty`, the derived
    // instance registers sound and the tuple decision reduces through restored
    // standard List constructors.
    let env = env_with(&[
        "inductive Pr where | mk : Nat -> Nat -> Pr deriving DecidableEq",
        "inductive Tri where | mk : Nat -> Nat -> Nat -> Tri deriving DecidableEq",
        TY_DECL,
    ]);
    assert_instance_sound(&env, "instTyDecidableEq");
    let one_int = "Ty.tuple (List.cons Ty.int List.nil)";
    let one_vec = "Ty.tuple (List.cons (Ty.vector 0) List.nil)";
    assert!(picks_equal(&env, one_int, one_int));
    assert!(!picks_equal(&env, one_int, one_vec));
}

/// Exact-name regression for restored `List` companion rules. A user primary
/// inductive below namespace `List` has constructors such as
/// `List.NamespaceTy.int`; those must remain primary rules, not be classified
/// as auxiliary merely by the `List.` prefix.
#[test]
fn list_namespace_primary_ctors_are_not_decidable_eq_companion_rules() {
    let env = env_with(&["namespace List \
         inductive NamespaceTy where \
         | int : NamespaceTy \
         | vector : Nat -> NamespaceTy \
         | tuple : List NamespaceTy -> NamespaceTy \
         deriving DecidableEq \
         end List"]);

    assert_instance_sound(&env, "instList.NamespaceTyDecidableEq");
    assert!(picks_equal(
        &env,
        "List.NamespaceTy.int",
        "List.NamespaceTy.int"
    ));
    assert!(!picks_equal(
        &env,
        "List.NamespaceTy.int",
        "List.NamespaceTy.vector 0"
    ));
    assert!(!picks_equal(
        &env,
        "List.NamespaceTy.tuple (List.cons List.NamespaceTy.int List.nil)",
        "List.NamespaceTy.tuple List.nil"
    ));
}
