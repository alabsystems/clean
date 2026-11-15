// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `attribute [..] ident` resolves its target in the module's OWN scope, the
//! way Lean's `realizeGlobalConstNoOverload` does
//! (`name_resolution::resolve_global_const_no_overload`).
//!
//! The command used to try the name as written at the root FIRST. So inside
//! `namespace N`, or after `open N`, `attribute [instance] c` bound a root `c`
//! whenever one was in the environment — in `clean check`/`clean project
//! check`, a root `c` defined by a sibling module the file does not even
//! import — and `theorem m : C.v = 3 := rfl` passed where Lean 4.8.0 rejects it
//! (round-24 verification of ff6c33c2c). Every expectation here was measured
//! on Lean 4.8.0 (2026-09-26).

use crate::test_support::file_verdicts::{run_file, verdict_of};

const CLASS: &str = "class C where\n  v : Nat\n";

/// Inside `namespace N`, `c` is `N.c` even when a root `c` exists (Lean 4.8.0
/// accepts `C.v = 2` here).
#[test]
fn inside_a_namespace_the_namespace_constant_wins() {
    let verdicts = run_file(&format!(
        "{CLASS}def c : C := ⟨3⟩\n\
         namespace N\n\
         def c : C := ⟨2⟩\n\
         attribute [instance] c\n\
         end N\n\
         theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// With `open N` at the root and both `c` and `N.c` in scope, Lean 4.8.0
/// refuses the command: `ambiguous identifier '`c', possible interpretations:
/// [N.c, c]`. No instance is registered, so neither value is provable.
#[test]
fn a_root_and_an_open_constant_are_ambiguous() {
    let verdicts = run_file(&format!(
        "{CLASS}def c : C := ⟨3⟩\n\
         namespace N\n\
         def c : C := ⟨2⟩\n\
         end N\n\
         open N\n\
         attribute [instance] c\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    let ambiguous = verdicts
        .iter()
        .find_map(|(_, verdict)| verdict.as_ref().err().filter(|e| e.contains("ambiguous")));
    assert!(
        ambiguous.is_some(),
        "the attribute must be refused: {verdicts:?}"
    );
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// With only `N.c`, `open N` makes `c` resolve to it.
#[test]
fn an_open_namespace_resolves_the_target() {
    let verdicts = run_file(&format!(
        "{CLASS}namespace N\n\
         def c : C := ⟨2⟩\n\
         end N\n\
         open N\n\
         attribute [instance] c\n\
         theorem is_two : C.v = 2 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
}

/// Enclosing namespaces are tried innermost first, and the first match wins
/// without ambiguity (Lean 4.8.0 binds `A.B.c` over `A.c` inside `A.B`).
#[test]
fn the_innermost_enclosing_namespace_wins() {
    let verdicts = run_file(&format!(
        "{CLASS}def A.c : C := ⟨3⟩\n\
         namespace A\n\
         namespace B\n\
         def c : C := ⟨2⟩\n\
         attribute [instance] c\n\
         end B\n\
         end A\n\
         theorem is_two : C.v = 2 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
}

// ---------------------------------------------------------------------------
// Round-25 verification of 3ee5ff78e: the resolver bound `protected` and
// another module's `private` declarations, which Lean never reaches through
// an atomic name. Every expectation below was measured on Lean 4.8.0
// (`scratchpad/round25/project-check/verify0/res`, `vb`).
// ---------------------------------------------------------------------------

use crate::test_support::file_verdicts::{run_modules, run_modules_unnamed};

/// res/protnsroot: inside `namespace N`, an atomic `c` does not reach
/// `protected def N.c`; it binds the root `c` (Lean accepts `C.v = 2`,
/// rejects `C.v = 3`). The resolver bound `N.c` and passed `C.v = 3`.
#[test]
fn a_protected_namespace_constant_is_not_reached_by_an_atomic_name() {
    let verdicts = run_file(&format!(
        "{CLASS}def c : C := ⟨2⟩\n\
         namespace N\n\
         protected def c : C := ⟨3⟩\n\
         attribute [instance] c\n\
         end N\n\
         theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// res/protns: with only a protected `N.c`, `attribute [instance] c` inside
/// `namespace N` is `unknown constant 'c'` in Lean, so nothing registers.
#[test]
fn a_protected_constant_alone_is_unknown_inside_its_namespace() {
    let verdicts = run_file(&format!(
        "{CLASS}namespace N\n\
         protected def c : C := ⟨3⟩\n\
         attribute [instance] c\n\
         end N\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// res/prot: `open N` does not bring a protected `N.c` into reach of `c`.
#[test]
fn a_simple_open_does_not_reach_a_protected_constant() {
    let verdicts = run_file(&format!(
        "{CLASS}namespace N\n\
         protected def c : C := ⟨3⟩\n\
         end N\n\
         open N\n\
         attribute [instance] c\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// res/protroot: after `open N`, a root `c` and a protected `N.c` are not
/// ambiguous — only the root one is reachable (Lean accepts `C.v = 2`).
#[test]
fn a_protected_open_constant_does_not_make_the_root_one_ambiguous() {
    let verdicts = run_file(&format!(
        "{CLASS}def c : C := ⟨2⟩\n\
         namespace N\n\
         protected def c : C := ⟨3⟩\n\
         end N\n\
         open N\n\
         attribute [instance] c\n\
         theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// The qualified name still reaches a protected declaration.
#[test]
fn a_qualified_name_reaches_a_protected_constant() {
    let verdicts = run_file(&format!(
        "{CLASS}namespace N\n\
         protected def c : C := ⟨3⟩\n\
         end N\n\
         attribute [instance] N.c\n\
         theorem is_three : C.v = 3 := rfl\n"
    ));
    assert!(verdict_of(&verdicts, "is_three").is_ok(), "{verdicts:?}");
}

/// vb/priv: another module's `private def c` is `unknown constant` to Lean
/// (its name is mangled with its module).
#[test]
fn another_modules_private_constant_is_not_an_attribute_target() {
    let verdicts = run_modules(&[
        &format!("{CLASS}private def c : C := ⟨3⟩\n"),
        "attribute [instance] c\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// vb/privroot: another module's private `N.c` does not make `c` ambiguous
/// after `open N`; the root `c` is bound (Lean accepts `C.v = 2`).
#[test]
fn another_modules_private_constant_does_not_make_a_target_ambiguous() {
    let verdicts = run_modules(&[
        &format!(
            "{CLASS}def c : C := ⟨2⟩\n\
             namespace N\n\
             private def c : C := ⟨3⟩\n\
             end N\n"
        ),
        "open N\n\
         attribute [instance] c\n\
         theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// The two tests above with no module names: the plain private `c` / `N.c`
/// is kept from the importer by the foreign-private filter alone.
#[test]
fn another_modules_private_constant_is_not_an_attribute_target_unnamed() {
    let verdicts = run_modules_unnamed(&[
        &format!("{CLASS}private def c : C := ⟨3⟩\n"),
        "attribute [instance] c\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
    let verdicts = run_modules_unnamed(&[
        &format!(
            "{CLASS}def c : C := ⟨2⟩\n\
             namespace N\n\
             private def c : C := ⟨3⟩\n\
             end N\n"
        ),
        "open N\n\
         attribute [instance] c\n\
         theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// A module's OWN private declaration stays an attribute target.
#[test]
fn the_modules_own_private_constant_is_an_attribute_target() {
    let verdicts = run_modules(&[
        CLASS,
        "private def c : C := ⟨3⟩\n\
         attribute [instance] c\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&verdicts, "is_three").is_ok(), "{verdicts:?}");
}

/// va/local: a top-level `local instance` is not exported; the importer
/// sees only the global one (Lean accepts `C.v = 2`, rejects `C.v = 3`).
#[test]
fn another_modules_local_instance_is_not_in_force() {
    let base = format!("{CLASS}instance i2 : C := ⟨2⟩\n");
    let verdicts = run_modules(&[
        &base,
        "local instance i3 : C := ⟨3⟩\n\
         theorem p : C.v = 3 := rfl\n",
        "theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&verdicts, "is_two").is_ok(), "{verdicts:?}");
    assert!(verdict_of(&verdicts, "is_three").is_err(), "{verdicts:?}");
}

/// va/scoped, va/scoped_open: an imported `scoped instance` is in force only
/// where its namespace is open.
#[test]
fn another_modules_scoped_instance_needs_its_namespace_open() {
    let exporter = format!(
        "{CLASS}instance i2 : C := ⟨2⟩\n\
         namespace N\n\
         scoped instance i3 : C := ⟨3⟩\n\
         end N\n\
         open N\n"
    );
    let closed = run_modules(&[
        &exporter,
        "theorem is_two : C.v = 2 := rfl\n\
         theorem is_three : C.v = 3 := rfl\n",
    ]);
    assert!(verdict_of(&closed, "is_two").is_ok(), "{closed:?}");
    assert!(verdict_of(&closed, "is_three").is_err(), "{closed:?}");
    let opened = run_modules(&[
        &exporter,
        "open N\n\
         theorem is_three : C.v = 3 := rfl\n\
         theorem is_two : C.v = 2 := rfl\n",
    ]);
    assert!(verdict_of(&opened, "is_three").is_ok(), "{opened:?}");
    assert!(verdict_of(&opened, "is_two").is_err(), "{opened:?}");
}
