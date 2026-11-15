// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `grind` reads `@[grind]` and its own `[...]` parameter list.
//!
//! Both were DROPPED: the parser mapped `@[grind]` to `Attribute::Unknown`,
//! and `grind` was registered `Nullary`, so `grind [no_such_lemma_xyzzy]` — a
//! name that does not exist — failed byte-identically to a bare `grind`.
//! Mathlib's `Function.update` is `@[grind] def update … := if h : a = a'
//! then … else f a` (Mathlib/Logic/Function/Basic.lean:524-527) and every
//! `by grind` row over it needs that definition unfolded before
//! `try_split_ite` has a condition to split on.
//!
//! The controls are the point of the file: the UNMARKED definition must still
//! fail (it fails in pinned Lean too, so the attribute is exactly the
//! difference, not a Clean weakness), and the `@[grind]` set must never reach
//! the ambient `@[simp]` set — Mathlib tags lemmas `@[grind]` that are
//! deliberately not `@[simp]`.
//!
//! Parsed the way `clean check` parses, with the builtin tactic patterns:
//! without them `grind [f]` reaches the generic expression-list path and `[f]`
//! is read as a list literal.

use crate::elaborate_decl_and_register_with_warning;
use crate::tactic::builtins::builtin_tactic_patterns;
use clean_kernel::env::GrindAttrKind;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_tactics;

/// Elaborate every declaration; return the first error's debug text.
fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// The shape of `Function.update`, prelude-only: a definition whose body is a
/// conditional, with a goal that is closed by unfolding it and splitting.
const TAGGED: &str = "@[grind] def pickG (P : Prop) [Decidable P] (a b : Nat) : Nat :=\n\
                      \x20 if P then a else b\n\
                      theorem pickG_same (P : Prop) [Decidable P] (a : Nat) : pickG P a a = a := by\n\
                      \x20 grind\n";

const UNTAGGED: &str = "def pickU (P : Prop) [Decidable P] (a b : Nat) : Nat :=\n\
                        \x20 if P then a else b\n";

#[test]
fn test_grind_attribute_unfolds_a_tagged_definition() {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, TAGGED) {
        panic!("`@[grind] def` must let grind unfold the definition: {e}");
    }
}

#[test]
fn test_grind_parameter_list_unfolds_an_untagged_definition() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{UNTAGGED}\
         theorem pickU_same (P : Prop) [Decidable P] (a : Nat) : pickU P a a = a := by\n\
         \x20 grind [pickU]\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`grind [pickU]` must use its parameter list: {e}");
    }
}

/// The control the whole class rests on: with neither the attribute nor the
/// parameter, grind cannot see through the definition and leaves the goal.
/// Pinned Lean v4.30.0-rc2 fails here too (`grind failed`), so this is parity,
/// not a Clean gap — and it is what makes the two tests above measure the
/// annotation rather than some unrelated improvement.
#[test]
fn test_grind_without_attribute_or_parameter_leaves_the_goal_open() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{UNTAGGED}\
         theorem pickU_same_bare (P : Prop) [Decidable P] (a : Nat) : pickU P a a = a := by\n\
         \x20 grind\n"
    );
    let err = elab(&mut env, &src)
        .expect("an opaque definition gives grind nothing to split on, as in Lean");
    assert!(
        err.contains("grind"),
        "the failure must come from grind, not from elaborating the fixture: {err}"
    );
}

/// `@[grind]` feeds the grind registry and NOTHING else. Mathlib tags lemmas
/// `@[grind]` that are deliberately not `@[simp]`, so a leak here would change
/// every `simp` call in a file that has one.
#[test]
fn test_grind_attribute_does_not_enter_the_ambient_simp_set() {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, TAGGED) {
        panic!("fixture must elaborate: {e}");
    }
    let pick = Name::anon().str("pickG");
    assert!(
        env.is_grind_lemma(&pick),
        "`@[grind] def pickG` must register in the grind set"
    );
    assert!(
        !env.is_simp_lemma(&pick),
        "`@[grind]` must NOT register a simp lemma"
    );
}

/// An unmodeled modifier is RECORDED and ignored, never rejected: `@[grind ←]`,
/// `@[grind cases]` and `@[grind ext]` all occur in Mathlib and elaborate
/// today. Recording the kind is what keeps a backward rule out of the
/// left-to-right rewriter.
#[test]
fn test_grind_modifiers_are_recorded_with_their_kind() {
    let mut env = Environment::with_prelude();
    let src = "@[grind =] theorem gEq (a : Nat) : Nat.succ a = Nat.succ a := rfl\n\
               @[grind ←] theorem gBwd (a : Nat) : Nat.succ a = Nat.succ a := rfl\n\
               @[grind →] theorem gFwd (a : Nat) : Nat.succ a = Nat.succ a := rfl\n\
               @[grind cases] theorem gCases (a : Nat) : Nat.succ a = Nat.succ a := rfl\n\
               @[grind ext] theorem gExt (a : Nat) : Nat.succ a = Nat.succ a := rfl\n\
               @[grind intro] theorem gIntro (a : Nat) : Nat.succ a = Nat.succ a := rfl\n\
               @[grind usr] theorem gUsr (a : Nat) : Nat.succ a = Nat.succ a := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("every `@[grind <mod>]` spelling must elaborate: {e}");
    }
    let kind = |s: &str| {
        env.grind_lemma_kind(&Name::anon().str(s))
            .unwrap_or_else(|| panic!("{s} must be registered"))
            .clone()
    };
    assert_eq!(kind("gEq"), GrindAttrKind::EqLhs);
    assert_eq!(kind("gBwd"), GrindAttrKind::Backward);
    assert_eq!(kind("gFwd"), GrindAttrKind::Forward);
    assert_eq!(kind("gCases"), GrindAttrKind::Cases);
    assert_eq!(kind("gExt"), GrindAttrKind::Ext);
    assert_eq!(kind("gIntro"), GrindAttrKind::Intro);
    assert_eq!(kind("gUsr"), GrindAttrKind::Unmodeled("usr".to_string()));
}

/// Only a LEFT-TO-RIGHT kind reaches the rewriter. A `←`-tagged definition is
/// registered and unused, so grind still cannot see through it — which is the
/// honest state, not a silent backwards rewrite.
#[test]
fn test_backward_grind_kind_is_not_used_as_a_left_to_right_rewrite() {
    assert!(GrindAttrKind::Infer.is_left_to_right_equation());
    assert!(GrindAttrKind::EqLhs.is_left_to_right_equation());
    for kind in [
        GrindAttrKind::Backward,
        GrindAttrKind::Forward,
        GrindAttrKind::Cases,
        GrindAttrKind::Ext,
        GrindAttrKind::Intro,
        GrindAttrKind::Unmodeled("symbol".to_string()),
    ] {
        assert!(
            !kind.is_left_to_right_equation(),
            "{kind:?} must not be handed to a left-to-right rewriter"
        );
    }

    let mut env = Environment::with_prelude();
    let src = "@[grind ←] def pickB (P : Prop) [Decidable P] (a b : Nat) : Nat :=\n\
               \x20 if P then a else b\n\
               theorem pickB_same (P : Prop) [Decidable P] (a : Nat) : pickB P a a = a := by\n\
               \x20 grind\n";
    let err = elab(&mut env, src).expect("a `←` registration must not unfold left to right");
    assert!(
        err.contains("grind"),
        "the failure must come from grind: {err}"
    );
    assert_eq!(
        env.grind_lemma_kind(&Name::anon().str("pickB")),
        Some(&GrindAttrKind::Backward),
        "the kind is still recorded"
    );
}

/// `attribute [grind] f` — the standalone command form, which Mathlib uses
/// where the definition and the tag are separated. It reaches the same
/// registry as the inline `@[grind]`, and the tagged definition is unfolded.
/// Pinned Lean v4.30.0-rc2 closes the same file.
#[test]
fn test_attribute_command_registers_a_grind_lemma() {
    let mut env = Environment::with_prelude();
    let src = "def pickA (P : Prop) [Decidable P] (a b : Nat) : Nat :=\n\
               \x20 if P then a else b\n\
               attribute [grind] pickA\n\
               theorem pickA_same (P : Prop) [Decidable P] (a : Nat) : pickA P a a = a := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`attribute [grind] f` must register f: {e}");
    }
    assert!(
        env.is_grind_lemma(&Name::anon().str("pickA")),
        "the command form must reach the same registry as `@[grind]`"
    );
}

/// REGRESSION. `grind only` SUPPRESSES the ambient `@[grind]` set.
///
/// `only` was consumed and dropped, so `grind only` behaved as a bare `grind`
/// and closed a goal pinned Lean v4.30.0-rc2 REFUSES: with `@[grind] def
/// pickG`, `by grind` succeeds and `by grind only` fails with
/// ``grind` failed … ⊢ False`. The marker the parser now emits is a GENERATED
/// name, which no source identifier can be.
#[test]
fn test_grind_only_does_not_use_the_environment_grind_set() {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, TAGGED) {
        panic!("the `@[grind]` fixture must elaborate: {e}");
    }
    let err = elab(
        &mut env,
        "theorem pickG_same_only (P : Prop) [Decidable P] (a : Nat) : pickG P a a = a := by\n\
         \x20 grind only\n",
    )
    .expect("`grind only` must not consult the environment set, as in Lean");
    assert!(
        err.contains("grind"),
        "the refusal must come from grind: {err}"
    );
}

/// …and `only` does not disable the tactic's OWN parameter list, which is the
/// whole point of the form. Pinned Lean v4.30.0-rc2 accepts this file.
#[test]
fn test_grind_only_still_uses_its_own_parameter_list() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{UNTAGGED}\
         theorem pickU_same_only (P : Prop) [Decidable P] (a : Nat) : pickU P a a = a := by\n\
         \x20 grind only [pickU]\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`grind only [f]` must still use `f`: {e}");
    }
}

/// The `only` marker is matched by SPELLING, not by structural equality.
///
/// `SurfaceName`'s `==` compares structural identity only, so a user lemma
/// literally named `_grind_only` would compare equal to the marker and silently
/// turn an ordinary `grind [_grind_only]` into `grind only` — which suppresses
/// the environment set and would stop closing this goal. The marker's component
/// origin is `Generated` and a source identifier's is `Plain`, which is what
/// `same_syntax` reads.
#[test]
fn test_a_user_lemma_named_like_the_only_marker_is_not_the_only_flag() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{TAGGED}\
         def _grind_only : Nat := 0\n\
         theorem pickG_same_marker (P : Prop) [Decidable P] (a : Nat) : pickG P a a = a := by\n\
         \x20 grind [_grind_only]\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("a user name spelled like the marker must stay an ordinary parameter: {e}");
    }
}
