// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! An IMPORTED `export` alias must be visible to TACTIC-side name resolution.
//!
//! Lean keeps ONE alias table. `aliasExtension` (`Lean/ResolveName.lean:68`) is
//! a `SimplePersistentEnvExtension`, so an `export` persists into the `.olean`
//! and an importing module reads it back exactly as the declaring module saw
//! it; `getAliases` (:85) is the single accessor and `resolveGlobalName` (:194)
//! consults it at :211 for every identifier. So `simp only [not_imp]`,
//! `rw [not_imp]` and the term `not_imp` all resolve through the same lookup.
//!
//! Clean keeps TWO: `NamespaceState`'s in-file table, which
//! `resolve_identifier` already consulted, and `Environment::export_aliases`,
//! decoded from an imported module's `Lean.aliasExtension`
//! (`clean_olean::import::load_register`), which only the TERM elaborator read
//! (`ElabCtx::resolve_ident`). Measured face of the gap, under `import Init`:
//! `simp only [not_imp]` reported "no progress" (the lemma was SILENTLY
//! dropped), `rw [not_imp]` reported "unknown identifier: not_imp", while the
//! TERM `not_imp` resolved — proving the alias was decoded and only the tactic
//! resolver missed it. The row is `Function.not_injective_iff`
//! (`Mathlib/Logic/Function/Basic.lean`), whose `not_forall` reaches the file
//! only through `export Classical (not_forall)` at
//! `Mathlib/Logic/Basic.lean:492`.
//!
//! These tests drive `resolve_identifier` directly against an environment
//! carrying a REGISTERED alias, which is the same state the olean decoder
//! leaves behind — no `import Init` run (30+ minutes in a debug build) is
//! needed to pin the resolution rule.

use crate::name_resolution::resolve_identifier;
use crate::namespace::NamespaceState;
use clean_kernel::env::Declaration;
use clean_kernel::env::Environment;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

/// Register `name : Prop` as an honest axiom so `get_const` finds it.
fn declare(env: &mut Environment, name: &Name) {
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("axiom registration");
}

fn surface(text: &str) -> clean_parser::SurfaceName {
    clean_parser::SurfaceName::generated_path(text)
}

#[test]
fn test_imported_export_alias_resolves_at_the_root() {
    let mut env = Environment::new();
    let target = Name::from_string("Classical.not_forall");
    declare(&mut env, &target);
    env.register_export_alias(Name::from_string("not_forall"), target.clone());

    let ns_state = NamespaceState::new();
    assert_eq!(
        resolve_identifier(&surface("not_forall"), &ns_state, &env),
        Some(target),
        "a root-level imported alias must resolve for every name-based tactic"
    );
}

#[test]
fn test_imported_export_alias_resolves_under_a_namespace_prefix() {
    // `export Foo (x)` inside `Foo` aliases `Foo.x`; Lean consults the alias
    // table at every prefix step of `resolveUsingNamespace`.
    let mut env = Environment::new();
    let target = Name::from_string("Other.helper");
    declare(&mut env, &target);
    env.register_export_alias(Name::from_string("Foo.helper"), target.clone());

    let mut ns_state = NamespaceState::new();
    ns_state.enter_namespace(Name::from_string("Foo"));
    assert_eq!(
        resolve_identifier(&surface("helper"), &ns_state, &env),
        Some(target),
        "the prefix walk must consult the imported alias table too"
    );
}

#[test]
fn test_a_real_constant_still_wins_over_an_imported_alias() {
    // Precedence is unchanged: a constant of that exact name wins.
    let mut env = Environment::new();
    let real = Name::from_string("not_forall");
    let aliased = Name::from_string("Classical.not_forall");
    declare(&mut env, &real);
    declare(&mut env, &aliased);
    env.register_export_alias(real.clone(), aliased);

    let ns_state = NamespaceState::new();
    assert_eq!(
        resolve_identifier(&surface("not_forall"), &ns_state, &env),
        Some(real),
        "an alias must never shadow a real constant of the same name"
    );
}

#[test]
fn test_an_imported_alias_to_a_missing_constant_mints_nothing() {
    let mut env = Environment::new();
    env.register_export_alias(
        Name::from_string("not_forall"),
        Name::from_string("Classical.not_forall"),
    );

    let ns_state = NamespaceState::new();
    assert_eq!(
        resolve_identifier(&surface("not_forall"), &ns_state, &env),
        None,
        "an alias whose target does not exist must fall through, never mint a name"
    );
}

#[test]
fn test_an_imported_alias_to_a_private_constant_outside_its_namespace_is_refused() {
    // The TERM path gates its alias hit on `is_const_accessible`; without the
    // same gate here a `private` target becomes reachable from a tactic that
    // could not name it before.
    let mut env = Environment::new();
    let target = Name::from_string("Secret.hidden");
    declare(&mut env, &target);
    env.mark_private(target.clone());
    env.register_export_alias(Name::from_string("hidden"), target);

    let ns_state = NamespaceState::new();
    assert_eq!(
        resolve_identifier(&surface("hidden"), &ns_state, &env),
        None,
        "a private target must stay unreachable through an alias"
    );
}

#[test]
fn test_an_imported_alias_to_a_private_constant_inside_its_namespace_resolves() {
    let mut env = Environment::new();
    let target = Name::from_string("Secret.hidden");
    declare(&mut env, &target);
    env.mark_private(target.clone());
    env.register_export_alias(Name::from_string("hidden"), target.clone());

    let mut ns_state = NamespaceState::new();
    ns_state.enter_namespace(Name::from_string("Secret"));
    assert_eq!(
        resolve_identifier(&surface("hidden"), &ns_state, &env),
        Some(target),
        "inside the declaring namespace the private target is nameable, alias or not"
    );
}
