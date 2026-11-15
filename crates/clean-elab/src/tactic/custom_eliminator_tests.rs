// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[induction_eliminator]` end to end: parse → elaborate → kernel-check.
//!
//! Each fixture was run through the pinned Lean v4.30.0-rc2; the verdict it
//! gave is stated on the test. A positive registers only after the kernel
//! accepted the assembled proof term; a negative control is a fixture Lean
//! REJECTS, so a Clean acceptance there is a false acceptance. A refusal where
//! Lean accepts is pinned as a refusal (`*_is_refused`), so it fails loudly the
//! day it is closed.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elab(code: &str) -> (Environment, Vec<Result<ElabResult, ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("fixture must parse");
    let results = decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect();
    (env, results)
}

fn errors(results: &[Result<ElabResult, ElabError>]) -> String {
    results
        .iter()
        .filter_map(|r| r.as_ref().err().map(|e| format!("{e}")))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn assert_all_ok(results: &[Result<ElabResult, ElabError>]) {
    assert!(
        results.iter().all(Result::is_ok),
        "every declaration must elaborate: {}",
        errors(results)
    );
}

/// A refusal recorded anywhere in the results, including inside a
/// `section` / `namespace` block's own result.
fn assert_nested_refusal(results: &[Result<ElabResult, ElabError>], needle: &str) {
    let text = format!("{results:?}");
    assert!(
        text.contains("Unsupported") && text.contains(needle),
        "expected a refusal mentioning {needle}"
    );
}

fn registered(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

/// Refused: `name` is not registered and some declaration failed with an
/// error mentioning `needle`.
fn assert_refused(
    env: &Environment,
    results: &[Result<ElabResult, ElabError>],
    name: &str,
    needle: &str,
) {
    assert!(
        !registered(env, name),
        "`{name}` must not register; errors: {}",
        errors(results)
    );
    let errs = errors(results);
    assert!(
        errs.contains(needle),
        "`{name}` must be refused with `{needle}`, got: {errs}"
    );
}

/// `tests/elab/eliminatorImplicitTargets.lean` of Lean v4.30.0-rc2, plus a
/// `_` alternative variant. Lean: accepts.
const EQUALITY: &str = r#"
inductive Equality {α : Type u} : α → α → Type u
| refl {a : α} : Equality a a

open Equality

@[induction_eliminator]
def ind {α : Type u} (motive : ∀ (a b : α) (p : Equality a b), Sort v)
  {a : α} (πrefl : motive a a refl) {b : α} (p : Equality a b) : motive a b p :=
@Equality.casesOn α a (λ b p => motive a a refl → motive a b p) b p
  (λ (ε : motive a a refl) => ε) πrefl
"#;

#[test]
fn test_induction_eliminator_implicit_targets_lean_fixture_registers() {
    let (env, results) = elab(&format!(
        "{EQUALITY}
def symm {{α : Type u}} {{a b : α}} (p : Equality a b) : Equality b a :=
by {{ induction p; apply refl }}

def symm2 {{α : Type u}} {{a b : α}} (p : Equality a b) : Equality b a :=
by induction p with | _ => apply refl
"
    ));
    assert_all_ok(&results);
    assert!(registered(&env, "symm") && registered(&env, "symm2"));
}

/// Lean: rejects (`Invalid target: Target (or one of its indices) occurs more
/// than once`) — both implicit targets solve to `a`.
#[test]
fn test_induction_eliminator_repeated_target_is_rejected() {
    let (env, results) = elab(&format!(
        "{EQUALITY}
def self' {{α : Type u}} {{a : α}} (p : Equality a a) : Equality a a :=
by {{ induction p; apply refl }}
"
    ));
    assert_refused(&env, &results, "self'", "occurs more than once");
}

/// Lean ACCEPTS (`generalizeVars` reverts `h`, which depends on the implicit
/// target `a`). Clean does not revert dependents of implicit targets and
/// refuses by name.
#[test]
fn test_induction_eliminator_dependent_of_implicit_target_is_refused() {
    let (env, results) = elab(&format!(
        "{EQUALITY}
def symm {{α : Type u}} {{a b : α}} (h : a = a) (p : Equality a b) : Equality b a :=
by {{ induction p; apply refl }}
"
    ));
    assert_refused(&env, &results, "symm", "depends on an implicit target");
}

const FOO: &str = r#"
inductive Foo where | a | b
"#;

const BY_ALL: &str = r#"
@[induction_eliminator] theorem Foo.byAll {motive : Foo → Prop} (h : ∀ x, motive x) (t : Foo) :
    motive t := h t
"#;

/// The proof works only with `Foo.byAll` (one case); `Foo.rec` leaves the
/// `b` case unsolved.
const ONE_CASE_PROOF: &str = r#"
theorem t1 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t
  exact h _
"#;

/// Lean: accepts both (the registry is on by default and when set `true`).
#[test]
fn test_induction_eliminator_registry_replaces_recursor() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}{ONE_CASE_PROOF}
set_option tactic.customEliminators true in
theorem t2 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t
  exact h _
"
    ));
    assert_all_ok(&results);
    assert!(registered(&env, "t1") && registered(&env, "t2"));
}

/// Lean: rejects (`unsolved goals case b`): with the option off `induction`
/// uses `Foo.rec`.
#[test]
fn test_custom_eliminators_option_false_in_decl_uses_recursor() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
set_option tactic.customEliminators false in{ONE_CASE_PROOF}"
    ));
    assert!(!registered(&env, "t1"), "{}", errors(&results));
}

/// Lean: rejects. File-scope option.
#[test]
fn test_custom_eliminators_option_false_at_file_scope_uses_recursor() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
set_option tactic.customEliminators false{ONE_CASE_PROOF}"
    ));
    assert!(!registered(&env, "t1"), "{}", errors(&results));
}

/// Lean: rejects. `set_option … in` inside a namespace, where Clean keeps the
/// value in the elaborator's local options.
#[test]
fn test_custom_eliminators_option_false_in_namespace_uses_recursor() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
namespace N
set_option tactic.customEliminators false in{ONE_CASE_PROOF}
theorem t2 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t
  exact h _
end N
"
    ));
    assert!(!registered(&env, "N.t1"), "{}", errors(&results));
    // Control: the option was scoped to `t1`; `t2` uses the registry.
    assert!(registered(&env, "N.t2"), "{results:?}");
}

/// Lean: rejects (`set_option` as a tactic and as a term). Clean today
/// refuses both forms at the `set_option` itself (`Unknown identifier`), which
/// is the verdict that matters here: the registry is never consulted with an
/// option value it was not shown.
#[test]
fn test_custom_eliminators_option_false_in_tactic_or_term_is_not_ignored() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
theorem t1 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  set_option tactic.customEliminators false in
  induction t
  exact h _
theorem t2 (t : Foo) (h : ∀ x : Foo, x = x) : t = t :=
  set_option tactic.customEliminators false in by
  induction t
  exact h _
"
    ));
    assert!(!registered(&env, "t1"), "{}", errors(&results));
    assert!(!registered(&env, "t2"), "{}", errors(&results));
}

/// Lean: rejects with `Too many targets for @Foo.imp`: the only target is
/// implicit, so `addImplicitTargets` treats it as implicit and the user's
/// target is one too many — through the registry and through `using`.
#[test]
fn test_induction_eliminator_implicit_only_target_is_rejected() {
    let imp = r#"
theorem Foo.imp {motive : Foo → Prop} (ha : motive .a) (hb : motive .b) {t : Foo} : motive t :=
  @Foo.rec motive ha hb t
"#;
    let (env, results) = elab(&format!(
        "{FOO}{imp}
attribute [induction_eliminator] Foo.imp
theorem t1 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t <;> exact h _
"
    ));
    assert_refused(&env, &results, "t1", "Too many targets");

    let (env, results) = elab(&format!(
        "{FOO}{imp}
theorem t2 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t using Foo.imp <;> exact h _
"
    ));
    assert_refused(&env, &results, "t2", "Too many targets");
}

/// Lean: accepts — the explicit-target twin of the fixture above, through the
/// registry and through `using`.
#[test]
fn test_induction_eliminator_explicit_target_control_registers() {
    let (env, results) = elab(&format!(
        "{FOO}
@[induction_eliminator] theorem Foo.exp {{motive : Foo → Prop}} (ha : motive .a) (hb : motive .b)
    (t : Foo) : motive t := @Foo.rec motive ha hb t
theorem t1 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t <;> exact h _
theorem t2 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t using Foo.exp <;> exact h _
"
    ));
    assert_all_ok(&results);
    assert!(registered(&env, "t1") && registered(&env, "t2"));
}

/// Lean: rejects (`Case tag a not found`): the local / scoped eliminator is
/// in force. Clean refuses the unmodeled kinds where they are written (the
/// refusal is recorded inside the `section` / `namespace` result; the theorem
/// after it then elaborates against `Foo.rec`, but the file is rejected).
#[test]
fn test_local_and_scoped_induction_eliminator_are_refused() {
    let unregistered = r#"
theorem Foo.byAll {motive : Foo → Prop} (h : ∀ x, motive x) (t : Foo) : motive t := h t
"#;
    let proof = r#"
theorem t1 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t
  case a => exact h _
  case b => exact h _
"#;
    let (_env, results) = elab(&format!(
        "{FOO}{unregistered}
section
attribute [local induction_eliminator] Foo.byAll{proof}end
"
    ));
    assert_nested_refusal(&results, "`local induction_eliminator`");

    let (_env, results) = elab(&format!(
        "{FOO}{unregistered}
namespace N
attribute [scoped induction_eliminator] Foo.byAll{proof}end N
"
    ));
    assert_nested_refusal(&results, "`scoped induction_eliminator`");
}

/// Lean: rejects (`Invalid alternative name wrong: Expected h`). Clean cannot
/// read the eliminator's binder names and refuses every named alternative.
#[test]
fn test_induction_eliminator_named_alternative_is_refused() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
theorem t1 (t : Foo) (hh : ∀ x : Foo, x = x) : t = t := by
  induction t with
  | wrong x => exact hh x
"
    ));
    assert_refused(
        &env,
        &results,
        "t1",
        "alternative names of a custom eliminator",
    );
}

/// Lean: rejects (`Case tag custom_eliminator_alt not found`): the case tag
/// Clean gives a registry eliminator's case is not spellable.
#[test]
fn test_induction_eliminator_case_tag_is_inaccessible() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
theorem t1 (t : Foo) (hh : ∀ x : Foo, x = x) : t = t := by
  induction t
  case custom_eliminator_alt => exact hh _
"
    ));
    assert!(!registered(&env, "t1"), "{}", errors(&results));
}

/// Lean ACCEPTS, using the LATEST registration (`Foo.exp`). Clean does not
/// keep registration order across imports and refuses the ambiguity by name.
#[test]
fn test_two_induction_eliminators_for_one_type_are_refused() {
    let (env, results) = elab(&format!(
        "{FOO}{BY_ALL}
@[induction_eliminator] theorem Foo.exp {{motive : Foo → Prop}} (ha : motive .a) (hb : motive .b)
    (t : Foo) : motive t := @Foo.rec motive ha hb t
theorem t1 (t : Foo) (h : ∀ x : Foo, x = x) : t = t := by
  induction t <;> exact h _
"
    ));
    assert_refused(&env, &results, "t1", "several `@[induction_eliminator]`");
}

/// Lean: rejects (`Expected resulting type of eliminator to be an application
/// of one of its parameters (the motive)`).
#[test]
fn test_induction_eliminator_on_a_non_eliminator_is_rejected() {
    let (_env, results) = elab(&format!(
        "{FOO}
@[induction_eliminator] theorem Foo.notElim (t : Foo) : t = t := rfl
"
    ));
    assert!(
        errors(&results).contains("Cannot add attribute [induction_eliminator]"),
        "{}",
        errors(&results)
    );
}
