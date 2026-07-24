// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick — destructuring a *dependent* `Exists` (and its bounded-exists / `And`
//! payload) via an anonymous constructor pattern `⟨x, hp, hq⟩`.
//!
//! The parser desugars `⟨x, hp, hq⟩` to a right-nested `Prod.mk x (Prod.mk hp
//! hq)` pattern. Against an `∃ x, p x ∧ q x` scrutinee, the outer field's type
//! is computed (via the `Prod.mk` placeholder) as the *bare predicate*
//! `β = fun x => p x ∧ q x` — an un-applied `Lam` with no nameable head — so the
//! nested-pattern machinery's `get_type_name` used to bail with
//! `NotImplemented("cannot extract type name from Lam(…)")` and NONE of these
//! declarations elaborated.
//!
//! The fix beta-reduces such a predicate field type against the already-bound
//! witness (`β x ≡ p x ∧ q x`, a `Const`-headed `And`) and remaps the nested
//! `Prod.mk` anonymous-tuple placeholder onto the field type's real sole
//! constructor (`And.intro`). Both steps are definitionally-equal / structural,
//! so every term below is still fully kernel-re-checked (asserted here by
//! registering into a real `Environment::with_prelude()` and requiring zero
//! elaboration/kernel failures).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
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

fn assert_registered(env: &Environment, short_names: &[&str]) {
    for short in short_names {
        assert!(
            env.constants()
                .any(|c| c.name.last_component().as_deref() == Some(*short)),
            "`{short}` was not registered (elaboration silently dropped it)"
        );
    }
}

/// The exact pattern that used to fail at `get_type_name(Lam(…))`: destructure a
/// dependent `∃ x, P x ∧ Q x` and rebuild it. Exercises the outer predicate
/// beta-reduction (`Exists`) AND the nested `Prod.mk → And.intro` remap.
#[test]
fn test_dependent_exists_and_anon_ctor_reconstruct_kernel_check() {
    let src = "
theorem exists_and_reconstruct (P Q : Nat → Prop) (h : ∃ x, P x ∧ Q x) :
    ∃ y, P y ∧ Q y :=
  match h with | ⟨x, hp, hq⟩ => ⟨x, hp, hq⟩
";
    let env = elaborate_module(src).expect("dependent ∃/∧ anon-ctor destructure must kernel-check");
    assert_registered(&env, &["exists_and_reconstruct"]);
}

/// Destructure the dependent `∃`/`∧` but keep only the first `And` component,
/// still through the anonymous constructor. The residual body is a plain `∃`
/// re-introduction whose predicate is fixed by the goal.
#[test]
fn test_dependent_exists_and_anon_ctor_drop_component_kernel_check() {
    let src = "
theorem exists_and_first (P Q : Nat → Prop) (h : ∃ x, P x ∧ Q x) : ∃ y, P y :=
  match h with | ⟨x, hp, hq⟩ => ⟨x, hp⟩
";
    let env = elaborate_module(src).expect("dependent ∃/∧ destructure (drop component) must check");
    assert_registered(&env, &["exists_and_first"]);
}

/// A trivial body proves the DESTRUCTURE itself is sound independent of the body
/// term — this is the minimal reproduction of the original
/// `cannot extract type name from Lam(…)` failure (the arm binds `x, hp, hq`
/// off `∃ x, P x ∧ Q x`).
#[test]
fn test_dependent_exists_and_anon_ctor_destructure_only_kernel_check() {
    let src = "
theorem exists_and_destructure_only (P Q : Nat → Prop) (h : ∃ x, P x ∧ Q x) : True :=
  match h with | ⟨x, hp, hq⟩ => True.intro
";
    let env = elaborate_module(src).expect("dependent ∃/∧ destructure (trivial body) must check");
    assert_registered(&env, &["exists_and_destructure_only"]);
}

/// Bounded-exists shape (`∃ x, x ∈ s ∧ P x`, the `BEx`/`∃ x ∈ s` desugaring):
/// the second `And` field `P x` is used in the rebuilt existential. The membership
/// predicate is modeled as an opaque `Mem : Nat → Prop` so the test needs no
/// `Membership` instance while keeping the same dependent-`And`-in-`Exists` shape.
#[test]
fn test_bounded_exists_shape_anon_ctor_kernel_check() {
    let src = "
theorem bex_shape (Mem P : Nat → Prop) (h : ∃ x, Mem x ∧ P x) : ∃ y, Mem y ∧ P y :=
  match h with | ⟨x, hmem, hp⟩ => ⟨x, hmem, hp⟩
";
    let env = elaborate_module(src).expect("bounded-∃ (Mem ∧ P) destructure must kernel-check");
    assert_registered(&env, &["bex_shape"]);
}
