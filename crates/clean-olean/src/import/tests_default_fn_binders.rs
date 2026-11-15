// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The binder-name table of imported `_default` functions, measured on the
//! pinned toolchain's `Init.Prelude` against `#print` output of the same
//! binary (see `default_fn_binders`).

use super::{default_fn_binder_idx, load_module_with_deps, DefaultFnBinderState};
use clean_kernel::env::Environment;
use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;

fn binders_of(env: &Environment, name: &str) -> Vec<(String, BinderInfo)> {
    let state = env
        .get_ext_state::<DefaultFnBinderState>(default_fn_binder_idx())
        .expect("the default-fn binder state is initialized by the loader");
    state
        .binders
        .get(&Name::interned(name))
        .unwrap_or_else(|| panic!("`{name}` should have a recorded binder table"))
        .iter()
        .map(|(n, bi)| (n.to_string(), *bi))
        .collect()
}

#[test]
fn test_init_prelude_default_fn_binders_are_the_used_fields_by_name() {
    let Some(lib) = crate::pinned_lean_lib_path() else {
        eprintln!(
            "Skipping test_init_prelude_default_fn_binders_are_the_used_fields_by_name: \
             pinned Lean toolchain (Init/Prelude.olean) not installed"
        );
        // SELF-SKIP OK: pinned Lean toolchain absent (external install); skip prints why
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // #print Applicative.seqLeft._default (v4.30.0-rc2):
    //   fun {f} map mapConst seq => @id (…) fun {α β} a b => @seq β α (@map α (β → α) (@Function.const α β) a) b
    // The binders are the structure parameter and the flattened FIELDS the
    // default abstracts, named after them — `pure` is not among them.
    assert_eq!(
        binders_of(&env, "Applicative.seqLeft._default"),
        vec![
            ("f".to_string(), BinderInfo::Implicit),
            ("map".to_string(), BinderInfo::Default),
            ("mapConst".to_string(), BinderInfo::Default),
            ("seq".to_string(), BinderInfo::Default),
        ]
    );
    // #print Applicative.map._default: fun {f} pure seq => …
    assert_eq!(
        binders_of(&env, "Applicative.map._default"),
        vec![
            ("f".to_string(), BinderInfo::Implicit),
            ("pure".to_string(), BinderInfo::Default),
            ("seq".to_string(), BinderInfo::Default),
        ]
    );
    // A closed default (`maxRecDepth : Nat := defaultMaxRecDepth`) has no
    // binders at all: `@id Nat Lean.defaultMaxRecDepth`.
    assert!(binders_of(&env, "Lean.Macro.Context.maxRecDepth._default").is_empty());
}
