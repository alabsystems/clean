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
//! 2. **Nested-`List Self`** — `tuple : List Ty -> Ty` is a NESTED inductive,
//!    for which Lean (4.8.0 and 4.30.0-rc2 alike) derives no `DecidableEq`: the
//!    clause refuses the class and the type is still declared. The companion
//!    kernel fix that makes `Ty.noConfusionType` reduce for the restored mutual
//!    type stays pinned.
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
// (2) Nested-`List Self`: Lean derives no `DecidableEq`, and neither does
//     Clean.
// ===================================================================
//
// Lean 4.8.0's `DecidableEq` handler declines a nested inductive (`mkDecEq`
// returns `false` on `isNested`, `Lean/Elab/Deriving/DecEq.lean`) and the
// default handler throws: pinned v4.8.0 on `TY_DECL` is "default handlers
// have not been implemented yet, class: 'DecidableEq' types: [Ty]", and
// v4.30.0-rc2 is "None of the deriving handlers for class `DecidableEq`
// applied to `Ty`". Clean's restored-companion builder
// (`decidable_eq_list_recursive.rs`) derived a sound instance anyway, which
// made Clean accept `if Ty.int = Ty.int then …` where Lean fails to
// synthesize `Decidable`. The clause now refuses the class up front
// (`infer::deriving_log`), so these pin the refusal; the type itself is still
// declared.

const TY_DECL: &str =
    "inductive Ty where | int | vector : Nat -> Ty | tuple : List Ty -> Ty deriving DecidableEq";

/// `decl` registered into `env`, with the failed-leaf errors its result
/// carries beside it.
fn register_with_failures(env: &mut Environment, decl: &str) -> Vec<String> {
    let parsed = parse_decl(decl).unwrap_or_else(|e| panic!("parse {decl:?}: {e:?}"));
    let result = elaborate_decl_and_register(env, &parsed)
        .unwrap_or_else(|e| panic!("register {decl:?}: {e:?}"));
    let mut failures = Vec::new();
    collect_failed(&result, &mut failures);
    failures
}

fn collect_failed(result: &crate::ElabResult, out: &mut Vec<String>) {
    match result {
        crate::ElabResult::Multiple(results) => {
            for r in results {
                collect_failed(r, out);
            }
        }
        crate::ElabResult::Failed { error, .. } => out.push(error.to_string()),
        _ => {}
    }
}

#[test]
fn listself_deriving_decidable_eq_refused_type_still_declared() {
    let mut env = Environment::with_prelude();
    let failures = register_with_failures(&mut env, TY_DECL);
    assert_eq!(failures.len(), 1, "{failures:?}");
    assert!(
        failures[0].contains("default handlers have not been implemented yet"),
        "{failures:?}"
    );
    assert!(env.get_const(&Name::from_string("Ty")).is_some());
    assert!(env.get_const(&Name::from_string("Ty.tuple")).is_some());
    assert!(
        env.get_const(&Name::from_string("instTyDecidableEq"))
            .is_none(),
        "Lean derives no DecidableEq for a nested inductive"
    );
}

#[test]
fn listself_decision_has_no_instance_refused() {
    let mut env = env_with(&[TY_DECL]);
    let d =
        parse_decl("def __pick : Nat := if (Ty.int = Ty.int) then 1 else 0").expect("parse pick");
    assert!(
        elaborate_decl_and_register(&mut env, &d).is_err(),
        "Lean 4.8.0: failed to synthesize `Decidable (Ty.int = Ty.int)`"
    );
}

#[test]
fn listself_noconfusion_type_reduces_for_mutual() {
    // The kernel-side fix: `Ty.noConfusionType False int (vector 0)` must reduce
    // to `False` for the MUTUAL `Ty` (it previously stuck on an under-applied
    // `Ty.casesOn`, blocking every `noConfusion`-based `isFalse`). The type is
    // declared whether or not its `deriving` clause succeeds.
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
fn listself_refused_with_preceding_flat_inductives_still_derived() {
    // Flat inductives before `Ty` still derive (Lean derives them too); the
    // nested one does not.
    let env = env_with(&[
        "inductive Pr where | mk : Nat -> Nat -> Pr deriving DecidableEq",
        "inductive Tri where | mk : Nat -> Nat -> Nat -> Tri deriving DecidableEq",
        TY_DECL,
    ]);
    assert_instance_sound(&env, "instPrDecidableEq");
    assert_instance_sound(&env, "instTriDecidableEq");
    assert!(env
        .get_const(&Name::from_string("instTyDecidableEq"))
        .is_none());
    assert!(!picks_equal(&env, "Pr.mk 1 2", "Pr.mk 1 3"));
}

/// The nested type under namespace `List` is refused too: the refusal keys
/// on the kernel's record of nesting, not on any `List.` name prefix.
#[test]
fn list_namespace_nested_decidable_eq_refused() {
    let mut env = Environment::with_prelude();
    let failures = register_with_failures(
        &mut env,
        "namespace List \
         inductive NamespaceTy where \
         | int : NamespaceTy \
         | vector : Nat -> NamespaceTy \
         | tuple : List NamespaceTy -> NamespaceTy \
         deriving DecidableEq \
         end List",
    );
    assert_eq!(failures.len(), 1, "{failures:?}");
    assert!(env
        .get_const(&Name::from_string("List.NamespaceTy"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("instList.NamespaceTyDecidableEq"))
        .is_none());
}
