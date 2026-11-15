// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! PIN: `@[to_dual …]` generates NOTHING, and the gap is silent.
//!
//! `@[to_dual]` (`Mathlib/Tactic/Translate/ToDual.lean:106`, over
//! `Mathlib/Tactic/Translate/Core.lean`) is the order-theoretic sibling of
//! `@[to_additive]`: at declaration time it walks the ELABORATED value, applies
//! a persistent name/argument translation dictionary, and `addDecl`s a second,
//! dual declaration. `Mathlib/Order/Basic.lean` carries it on 116 of its 204
//! declarations and then USES the names it mints later in the same file —
//! `Eq.ge` (from `@[to_dual ge] alias Eq.le := le_of_eq`, L145) at L211 and
//! L217, `LE.le.trans'` (L135) at L302, `LE.le.trans_lt'` (L137) at L305. None
//! of those four names has any other producer anywhere in Mathlib or in the
//! pinned toolchain's own sources.
//!
//! Clean tolerates the attribute as a no-op (`ensure_known_attributes`,
//! `crates/clean-elab/src/infer/elab_attributes.rs`), so the carrier
//! declaration is ACCEPTED and its dual is simply absent; the later use then
//! fails as an unknown identifier, several hundred lines away from the cause.
//! Pinned lean without Mathlib is STRICTER — it rejects the attribute outright
//! ("Unknown attribute `[to_dual]`") — so Clean is lenient in the one direction
//! that hides the defect.
//!
//! WHY THIS IS A PIN AND NOT A FIX. Minting the dual correctly needs Mathlib's
//! translation DICTIONARY, which is a persistent environment extension carried
//! in the `.olean` (`Eq.ge`'s value is `ge_of_eq`, itself minted by a
//! `@[to_dual]` in an imported module, not derivable from `le_of_eq` by any
//! spelling rule). A name-substitution heuristic would mint well-typed WRONG
//! theorems that Mathlib then builds on, which is strictly worse than the
//! missing name. Refusing the carrier declaration instead is not free either:
//! at least 41 currently-PASSING declarations in `Mathlib/Order/Basic.lean`
//! alone carry the attribute, so that trade is a ratchet re-arm and an owner
//! decision, not a four-row cleanup.
//!
//! TARGET ASSERTION. The day a dual-generation pass lands, this test FAILS at
//! `dual_name_is_not_minted` and must be rewritten to assert the dual's
//! STATEMENT, not merely its existence.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_parser::parse_file;

fn elaborate_module(source: &str) -> (Environment, Vec<String>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("the pin's source must parse");
    let mut failures = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register(&mut env, &processed) {
            Ok(result) => collect_failures(&result, &mut failures),
            Err(error) => failures.push(error.to_string()),
        }
    }
    (env, failures)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// The carrier declaration is accepted and mints nothing.
#[test]
fn test_to_dual_carrier_is_accepted_and_the_dual_name_is_not_minted() {
    let (env, failures) = elaborate_module(
        "
@[to_dual base_ge] theorem base_le : True := True.intro
",
    );
    assert!(
        failures.is_empty(),
        "the carrier declaration is tolerated today; got {failures:?}"
    );
    assert!(
        env.get_const(&Name::from_string("base_le")).is_some(),
        "the carrier itself must be registered"
    );
    // TARGET ASSERTION — invert this the day `@[to_dual]` generates.
    assert!(
        env.get_const(&Name::from_string("base_ge")).is_none(),
        "`@[to_dual]` mints nothing today; if this now holds a constant, the \
         dual-generation pass has landed and this pin must be rewritten to \
         assert the dual's STATEMENT"
    );
}

/// The consequence the four `Mathlib/Order/Basic.lean` rows record: a use of
/// the un-minted dual name, later in the SAME file, is an unknown identifier.
#[test]
fn test_using_the_un_minted_dual_name_fails() {
    let (_, failures) = elaborate_module(
        "
@[to_dual base_ge] theorem base_le : True := True.intro
theorem uses_dual : True := base_ge
",
    );
    assert!(
        failures.iter().any(|f| f.contains("base_ge")),
        "the use of the un-minted dual must fail by NAME; got {failures:?}"
    );
}

/// CONTROL: arbitrary unregistered names are errors, while the explicitly
/// recognized `to_dual` name above retains its independently pinned gap.
#[test]
fn test_an_undeclared_attribute_is_refused_by_name() {
    let (env, failures) =
        elaborate_module("@[some_unknown_attr foo] theorem refused : True := True.intro\n");
    assert!(
        failures.iter().any(|f| f.contains("some_unknown_attr")),
        "an undeclared attribute must fail by name; got {failures:?}"
    );
    assert!(env.get_const(&Name::from_string("refused")).is_none());
}
