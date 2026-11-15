// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three fixes from the verified diagnosis workflow (2026-09-12), each fixture
//! accepted by the pinned v4.30.0-rc2 binary:
//! - a class-typed local introduced by a TACTIC (`have`, `intro`) is a local
//!   instance, as Lean's `withNewLocalInstances` makes it;
//! - Mathlib's `inhabit α` asserts `inhabited_h : Inhabited α` from a
//!   `Nonempty α` in scope;
//! - an omitted CLASS parent of a structure instance is synthesized before
//!   defaults are consulted (Lean's `addParentInstanceFields`).

use crate::elaborate_decl_and_register_with_warning;
use crate::FileContext;
use crate::{elaborate_decl_and_register_with_context, preprocess_decl_with_context};
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

fn elab_in_file(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut file_ctx = FileContext::new();
    for d in &decls {
        let processed = preprocess_decl_with_context(d, &mut file_ctx);
        if let Err(e) = elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_class_typed_tactic_locals_are_local_instances() {
    let mut env = Environment::with_prelude();
    let src = "theorem hv1 (α : Type) (h : Nonempty α) : Nonempty α := by\n\
               \x20 have : Inhabited α := ⟨Classical.choice h⟩\n\
               \x20 exact ⟨default⟩\n\
               theorem hv2 (α : Type) (h : Nonempty α) : Nonempty α := by\n\
               \x20 have inst : Inhabited α := ⟨Classical.choice h⟩\n\
               \x20 exact ⟨@default α inst⟩\n\
               theorem hvIntro (α : Type) : Inhabited α → Nonempty α := by\n\
               \x20 intro inst\n\
               \x20 exact ⟨default⟩\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a class-typed `have`/`intro` local must answer instance search: {e}");
    }
}

#[test]
fn test_inhabit_asserts_an_inhabited_instance_from_nonempty() {
    let mut env = Environment::with_prelude();
    let src = "theorem inh1 (α : Sort u) [Nonempty α] : Nonempty α := by\n\
               \x20 inhabit α\n\
               \x20 exact ⟨default⟩\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`inhabit α` must assert `Inhabited α`: {e}");
    }
}

#[test]
fn test_inhabit_without_a_nonempty_in_scope_fails_closed() {
    let mut env = Environment::with_prelude();
    let src = "theorem noWitness (α : Type) : True := by\n\
               \x20 inhabit α\n\
               \x20 trivial\n";
    assert!(
        elab(&mut env, src).is_some(),
        "`inhabit` with no `Nonempty α` in scope must fail, not guess"
    );
}

/// `Foo`, `Box` and their GLOBAL `Nonempty` instances — no local hypothesis
/// anywhere. `boxNe` is parametric, so it answers only through a sub-goal.
///
/// Both preludes already register `Nonempty` as a class. Keep the actual Lean
/// source here: repeating `attribute [class] Nonempty` is a duplicate error.
const GLOBAL_NONEMPTY: &str = "axiom Foo : Type\n\
                               axiom fooNe : Nonempty Foo\n\
                               attribute [instance] fooNe\n\
                               axiom Box : Type → Type\n\
                               axiom boxNe (α : Type) [Nonempty α] : Nonempty (Box α)\n\
                               attribute [instance] boxNe\n\
                               axiom Bar : Type\n";

/// Mathlib's `evalInhabit` is `synthInstance (Nonempty α)`, so a GLOBAL
/// instance answers `inhabit` with no `Nonempty` local in scope: a ground one
/// (`g1`), a parametric one whose premise is a local binder (`g2`) and one
/// whose premise is itself global (`g3`). The bare handler scanned the goal's
/// locals only and refused all three. Ground truth: the pinned v4.30.0-rc2
/// `lean` with `import Mathlib.Tactic.Inhabit` accepts `g1`–`g3` as written.
#[test]
fn test_inhabit_global_nonempty_instance_is_synthesized() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{GLOBAL_NONEMPTY}\
         theorem g1 : Nonempty Foo := by\n\
         \x20 inhabit Foo\n\
         \x20 exact ⟨default⟩\n\
         theorem g2 (α : Type) [Nonempty α] : Nonempty (Box α) := by\n\
         \x20 inhabit Box α\n\
         \x20 exact ⟨default⟩\n\
         theorem g3 : Nonempty (Box Foo) := by\n\
         \x20 inhabit Box Foo\n\
         \x20 exact ⟨default⟩\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`inhabit` must synthesize `Nonempty _` from a GLOBAL instance: {e}");
    }
}

/// The resolver route invents nothing: at a carrier with no instance (`Bar`),
/// and at one whose parametric premise has none (`Box Bar`), `inhabit` still
/// fails. The pinned `lean` refuses both: `failed to synthesize Nonempty Bar`
/// / `Nonempty (Box Bar)`.
#[test]
fn test_inhabit_global_instance_at_other_carrier_fails_closed() {
    for (name, carrier) in [("bad", "Bar"), ("bad2", "Box Bar")] {
        let mut env = Environment::with_prelude();
        if let Some(e) = elab(&mut env, GLOBAL_NONEMPTY) {
            panic!("the fixture's declarations must register: {e}");
        }
        let src = format!(
            "theorem {name} : True := by\n\
             \x20 inhabit {carrier}\n\
             \x20 trivial\n"
        );
        let err = elab(&mut env, &src)
            .unwrap_or_else(|| panic!("`inhabit {carrier}` has no `Nonempty` instance"));
        assert!(
            err.contains("Nonempty"),
            "`{name}`: the refusal must name the missing `Nonempty` instance: {err}"
        );
    }
}

#[test]
fn test_an_omitted_class_parent_is_synthesized_before_defaults() {
    let mut env = Environment::with_prelude();
    let src = "structure Unique' (α : Sort u) extends Inhabited α where\n\
               \x20 uniq : ∀ a : α, a = default\n\
               attribute [class] Unique'\n\
               structure Box where\n\
               \x20 x : Nat\n\
               instance : Inhabited Box := ⟨⟨0⟩⟩\n\
               axiom box_uniq : ∀ a : Box, a = default\n\
               instance boxU : Unique' Box where\n\
               \x20 uniq := box_uniq\n\
               instance boxUCtl : Unique' Box where\n\
               \x20 default := ⟨0⟩\n\
               \x20 uniq := box_uniq\n";
    if let Some(e) = elab_in_file(&mut env, src) {
        panic!("the omitted `Inhabited` parent must come from instance synthesis: {e}");
    }
}
