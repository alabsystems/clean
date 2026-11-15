// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `∀`-binder-name table of imported definitions' VALUES, measured on the
//! pinned toolchain's own `.olean` files through the loader (the direct,
//! zero-copy path `clean check` imports with) against `#print` output of the
//! same binary (see `value_binder_names`).

use super::load_module_with_deps;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

#[test]
fn test_init_data_function_injective_value_names_its_strict_implicit_binders() {
    // SELF-SKIP OK: needs the pinned Lean toolchain's .olean lib (Init/Data/Function.olean
    // via CLEAN_OLEAN_PINNED_LEAN_LIB or the elan pin); absent on boxes without it; skip is logged
    let Some(lib) = crate::pinned_lean_lib_path() else {
        eprintln!("Skipping test: pinned toolchain not installed");
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Data.Function", &[lib])
        .expect("Init.Data.Function should import");

    // #print Function.Injective (v4.30.0-rc2):
    //   def Function.Injective.{u_1, u_2} : {α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop :=
    //   fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
    let injective = env
        .get_value_forall_binder_names(&Name::interned("Function.Injective"))
        .expect("`Function.Injective`'s value is a `∀` under three lambdas");
    assert_eq!(injective.lambdas, 3);
    let names: Vec<String> = injective.names.iter().map(ToString::to_string).collect();
    assert_eq!(names.len(), 3, "a₁, a₂ and the arrow's binder: {names:?}");
    assert_eq!(&names[..2], ["a₁".to_string(), "a₂".to_string()]);

    //   def Function.Surjective … := fun {α} {β} f => ∀ (b : β), ∃ a, f a = b
    let surjective = env
        .get_value_forall_binder_names(&Name::interned("Function.Surjective"))
        .expect("`Function.Surjective`'s value is a `∀` under three lambdas");
    assert_eq!(surjective.lambdas, 3);
    assert_eq!(
        surjective
            .names
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        vec!["b".to_string()]
    );

    // A definition whose value is not a `∀` records nothing
    // (`Function.comp := fun f g x => f (g x)`).
    assert!(env
        .get_value_forall_binder_names(&Name::interned("Function.comp"))
        .is_none());
}
