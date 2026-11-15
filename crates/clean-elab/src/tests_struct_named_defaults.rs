// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean-shaped structure-field defaults are applied BY NAME, deferred until
//! the fields they name exist, and build an omitted parent subobject — the
//! three behaviors `infer/elab_struct_default.rs` documents against the
//! pinned Lean's `#print` output. Each arm hand-registers a `_default`
//! function in Lean's exact shape (`fun {α} le => @id T body`) together with
//! its binder-name table, the way the `.olean` importer would.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::env::Declaration;
use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_olean::{default_fn_binder_idx, DefaultFnBinderState};
use clean_parser::parse_file;

/// Elaborate every declaration in `src`, returning the first error (as its
/// `Debug` rendering) or `None` when all of them registered and kernel-checked.
fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// Re-register the source-elaborated `from` under Lean's default-function
/// name `to` (`<Struct>.<field>._default`), and record its binder names —
/// what `clean_olean::default_fn_binders` does for an imported one.
fn install_default_fn(env: &mut Environment, from: &str, to: &str, binders: &[(&str, BinderInfo)]) {
    let info = env
        .get_const(&Name::from_string(from))
        .unwrap_or_else(|| panic!("`{from}` must be registered"))
        .clone();
    env.add_decl(Declaration::Definition {
        name: Name::from_string(to),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
        value: info.value.clone().expect("a definition has a value"),
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("`{to}` must register: {e:?}"));
    env.get_ext_state_mut::<DefaultFnBinderState>(default_fn_binder_idx())
        .binders
        .insert(
            Name::from_string(to),
            binders
                .iter()
                .map(|(n, bi)| (Name::from_string(n), *bi))
                .collect(),
        );
}

fn value_of(env: &Environment, name: &str) -> String {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"));
    format!(
        "{:?}",
        info.value.as_ref().expect("a definition has a value")
    )
}

/// `structure P` whose `lt` default uses `le` but NOT the field between them:
/// positional application (`P.lt._default Nat le eq`) is ill-typed, by-name
/// application is Lean's.
const P: &str = "structure P (a : Type) where\n  le : a -> a -> Prop\n  eq : a -> a -> Prop\n  lt : a -> a -> Prop\n\
def P_lt_default {a : Type} (le : a -> a -> Prop) : a -> a -> Prop :=\n  id (fun x y => And (le x y) (Not (le y x)))\n";

#[test]
fn test_named_default_binds_fields_by_name_not_position() {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, P) {
        panic!("fixture must elaborate: {e}");
    }
    install_default_fn(
        &mut env,
        "P_lt_default",
        "P.lt._default",
        &[("a", BinderInfo::Implicit), ("le", BinderInfo::Default)],
    );
    let src = "def pNat : P Nat := { le := fun x y => x = y, eq := fun x y => x = y }\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`lt` must be filled from `P.lt._default` applied by name: {e}");
    }
    let value = value_of(&env, "pNat");
    assert!(
        value.contains("\"And\"") && !value.contains("_default"),
        "Lean substitutes the default's BODY (the `id` marker stripped), never an \
         application of the `_default` constant; got {value}"
    );
}

#[test]
fn test_named_default_without_a_binder_table_falls_back_to_the_positional_rule_and_fails() {
    // Control for the arm above: the same `_default` with NO binder table is
    // treated as Clean-native and applied positionally — `P.lt._default Nat
    // le eq` — which is ill-typed and must be refused, not accepted.
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, P) {
        panic!("fixture must elaborate: {e}");
    }
    install_default_fn(&mut env, "P_lt_default", "P.lt._default", &[]);
    env.get_ext_state_mut::<DefaultFnBinderState>(default_fn_binder_idx())
        .binders
        .remove(&Name::from_string("P.lt._default"));
    let src = "def pNat : P Nat := { le := fun x y => x = y, eq := fun x y => x = y }\n";
    assert!(
        elab(&mut env, src).is_some(),
        "positional application of a Lean-shaped default is ill-typed and must fail"
    );
}

#[test]
fn test_named_default_using_a_later_field_is_deferred_and_resolved() {
    // `Q.lt._default` uses `le`, which comes AFTER `lt` in constructor order:
    // Lean's `propagateLoop` fixpoint resolves it once `le` exists.
    let q = "structure Q (a : Type) where\n  lt : a -> a -> Prop\n  le : a -> a -> Prop\n\
def Q_lt_default {a : Type} (le : a -> a -> Prop) : a -> a -> Prop :=\n  id (fun x y => le x y)\n";
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, q) {
        panic!("fixture must elaborate: {e}");
    }
    install_default_fn(
        &mut env,
        "Q_lt_default",
        "Q.lt._default",
        &[("a", BinderInfo::Implicit), ("le", BinderInfo::Default)],
    );
    let src = "def qNat : Q Nat := { le := fun x y => x = y }\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`lt` must be defaulted after `le` is built (fixpoint): {e}");
    }
    let value = value_of(&env, "qNat");
    assert!(
        !value.contains("_default"),
        "the deferred default must be substituted, not left as an application: {value}"
    );
}

#[test]
fn test_omitted_parent_subobject_is_built_from_the_child_default() {
    // `Pre extends LTc`; a `Pre` literal that gives only `le` must build
    // `toLTc` as `LTc.mk (fun x y => le x y ∧ ¬ le y x)` from `Pre.lt._default`
    // — the CHILD's default for the PARENT's field, found child-first — with
    // `le` a LATER slot than `toLTc`, so the leaf is deferred and resolved by
    // the tree's fixpoint. This is `Pi.preorder`'s shape (`toLT` from
    // `Preorder.lt._default`), measured on Mathlib.
    let pre = "structure LTc (a : Type) where\n  lt : a -> a -> Prop\n\
structure Pre (a : Type) extends LTc a where\n  le : a -> a -> Prop\n\
def Pre_lt_default {a : Type} (le : a -> a -> Prop) : a -> a -> Prop :=\n  id (fun x y => And (le x y) (Not (le y x)))\n";
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, pre) {
        panic!("fixture must elaborate: {e}");
    }
    install_default_fn(
        &mut env,
        "Pre_lt_default",
        "Pre.lt._default",
        &[("a", BinderInfo::Implicit), ("le", BinderInfo::Default)],
    );
    let src = "def preNat : Pre Nat := { le := fun x y => x = y }\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`toLTc` must be built from `Pre.lt._default` by name: {e}");
    }
    let value = value_of(&env, "preNat");
    assert!(
        value.contains("[\"LTc\", \"mk\"]")
            && value.contains("\"And\"")
            && !value.contains("_default"),
        "expected `Pre.mk Nat (LTc.mk Nat (fun x y => And …)) le`, got {value}"
    );
}
