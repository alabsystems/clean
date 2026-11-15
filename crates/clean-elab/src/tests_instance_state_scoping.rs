// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's INSTANCE STATE is scoped: one state per open section / namespace
//! block, a `local` entry / erase / namespace activation touching only the
//! innermost one, a global entry touching all of them, each state's index
//! keeping an instance where it was first inserted (`crate::instance_store`).
//! Round-25 verification of 100c3ccca found `clean check` and `clean project
//! check` crediting values Lean 4.8.0 never computes wherever that model was
//! missing; the verification of fbbb586e0 found an erased-and-re-added
//! instance made the NEWEST (Lean keeps it in place: `eraseCore` leaves the
//! tree entry, `insertVal` replaces it). Every expectation below was measured
//! on Lean 4.8.0 (2026-09-26); the model is exact, so each pins the one value
//! Lean computes and refuses the others.

use crate::test_support::file_verdicts::{run_file, run_modules, verdict_of};

const B: &str = "class C where\n  v : Nat\ninstance ib : C := ⟨1⟩\n";

fn accepted(verdicts: &[(String, Result<(), String>)], name: &str) -> bool {
    verdict_of(verdicts, name).is_ok()
}

/// No declaration named `name` was accepted, and some declaration failed with
/// a type mismatch naming `expected` — a failing `open N in theorem t` is
/// reported against the `open` command, not under `t`'s name.
fn refused_with(verdicts: &[(String, Result<(), String>)], name: &str, expected: &str) -> bool {
    let dotted = format!(".{name}");
    !verdicts
        .iter()
        .any(|(n, v)| (n == name || n.ends_with(&dotted)) && v.is_ok())
        && verdicts.iter().any(|(_, v)| {
            v.as_ref()
                .err()
                .is_some_and(|e| e.contains("TypeMismatch") && e.contains(expected))
        })
}

/// `P: local instance i3`, `M: import P; attribute [instance] i3`: the
/// global addition appends i3 (it is absent from M's state), so it is M's
/// newest instance (Lean: 3; round-25 `locsame_1` credited 1).
#[test]
fn an_imported_local_instance_re_added_globally_is_the_newest() {
    let verdicts = run_modules(&[
        B,
        "local instance i3 : C := ⟨3⟩\n",
        "attribute [instance] i3\n\
         theorem is_three : C.v = 3 := rfl\n\
         theorem is_one : C.v = 1 := rfl\n",
    ]);
    assert!(accepted(&verdicts, "is_three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "is_one"), "{verdicts:?}");
}

/// The same-file shape: a `local instance` whose section ended, re-added
/// globally (round-25 `locsame1_1`).
#[test]
fn an_ended_local_instance_re_added_globally_is_the_newest() {
    let verdicts = run_file(&format!(
        "{B}section\nlocal instance i3 : C := ⟨3⟩\nend\n\
         attribute [instance] i3\n\
         theorem is_three : C.v = 3 := rfl\n\
         theorem is_one : C.v = 1 := rfl\n"
    ));
    assert!(accepted(&verdicts, "is_three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "is_one"), "{verdicts:?}");
}

/// `open scoped N` activates an imported `scoped instance` (Lean: 3;
/// round-25 `openscoped_1` credited 1), and brings no name into scope.
#[test]
fn open_scoped_activates_an_imported_scoped_instance() {
    let verdicts = run_modules(&[
        B,
        "namespace N\nscoped instance i3 : C := ⟨3⟩\nend N\n",
        "open scoped N\n\
         theorem is_three : C.v = 3 := rfl\n\
         theorem is_one : C.v = 1 := rfl\n",
    ]);
    assert!(accepted(&verdicts, "is_three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "is_one"), "{verdicts:?}");
}

/// Activation ADDS the scoped instances to the state now, so each is the
/// newest of its tier: with P's scoped `i3` and Q's global `i4`, `open N`
/// in M takes i3, and without it i4 (Lean: 4, then 3).
#[test]
fn activation_makes_the_scoped_instance_the_newest() {
    let verdicts = run_modules(&[
        B,
        "namespace N\nscoped instance i3 : C := ⟨3⟩\nend N\ninstance i4 : C := ⟨4⟩\n",
        "theorem before_four : C.v = 4 := rfl\n\
         theorem before_three : C.v = 3 := rfl\n\
         open N\n\
         theorem after_three : C.v = 3 := rfl\n\
         theorem after_four : C.v = 4 := rfl\n",
    ]);
    assert!(accepted(&verdicts, "before_four"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "before_three"), "{verdicts:?}");
    assert!(accepted(&verdicts, "after_three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "after_four"), "{verdicts:?}");
}

/// Re-entering a namespace re-activates it: `namespace N; scoped instance
/// i3; end N; instance i4; namespace N` resolves to 3 inside (Lean: 3).
#[test]
fn re_entering_a_namespace_re_activates_its_scoped_instances() {
    let verdicts = run_file(&format!(
        "{B}namespace N\nscoped instance i3 : C := ⟨3⟩\nend N\n\
         instance i4 : C := ⟨4⟩\n\
         namespace N\n\
         theorem inside_three : C.v = 3 := rfl\n\
         theorem inside_four : C.v = 4 := rfl\n\
         end N\n\
         theorem outside_four : C.v = 4 := rfl\n"
    ));
    assert!(accepted(&verdicts, "N.inside_three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "N.inside_four"), "{verdicts:?}");
    assert!(accepted(&verdicts, "outside_four"), "{verdicts:?}");
}

/// `open N hiding x` activates `N`'s scoped instances; `open N (x)` and
/// `open N renaming x → z` do not (Lean: 3, 4, 4).
#[test]
fn only_the_simple_and_hiding_opens_activate() {
    let scoped = "namespace N\nscoped instance i3 : C := ⟨3⟩\ndef x : Nat := 7\nend N\n\
                  instance i4 : C := ⟨4⟩\n";
    let verdicts = run_file(&format!(
        "{B}{scoped}section\nopen N hiding x\n\
         theorem hiding_three : C.v = 3 := rfl\nend\n\
         section\nopen N (x)\n\
         theorem explicit_four : C.v = 4 := rfl\n\
         theorem explicit_three : C.v = 3 := rfl\nend\n\
         section\nopen N renaming x → z\n\
         theorem renaming_four : C.v = 4 := rfl\n\
         theorem renaming_three : C.v = 3 := rfl\nend\n"
    ));
    assert!(accepted(&verdicts, "hiding_three"), "{verdicts:?}");
    assert!(accepted(&verdicts, "explicit_four"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "explicit_three"), "{verdicts:?}");
    assert!(accepted(&verdicts, "renaming_four"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "renaming_three"), "{verdicts:?}");
}

/// `open scoped N in e` activates `N`'s scoped instances for `e` and opens no
/// name: with a root `x := 2` and `N.x := 7`, `(open scoped N in x) = 2`
/// (Lean accepts it; Clean used to open the names too).
#[test]
fn term_open_scoped_opens_no_names() {
    let verdicts = run_file(&format!(
        "{B}namespace N\nscoped instance i3 : C := ⟨3⟩\ndef x : Nat := 7\nend N\n\
         def x : Nat := 2\n\
         theorem root_x : (open scoped N in x) = 2 := rfl\n\
         theorem n_x : (open scoped N in x) = 7 := rfl\n\
         theorem scoped_three : (open scoped N in (C.v : Nat)) = 3 := rfl\n\
         theorem scoped_one : (open scoped N in (C.v : Nat)) = 1 := rfl\n"
    ));
    assert!(accepted(&verdicts, "root_x"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "n_x"), "{verdicts:?}");
    assert!(accepted(&verdicts, "scoped_three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "scoped_one"), "{verdicts:?}");
}

/// `attribute [-instance]` erases from the current scope only: inside the
/// section `i4` is gone (Lean: 1), after `end` it is back (Lean: 4).
#[test]
fn an_erase_ends_with_its_section() {
    let verdicts = run_file(&format!(
        "{B}instance i4 : C := ⟨4⟩\n\
         section\nattribute [-instance] i4\n\
         theorem inside_one : C.v = 1 := rfl\n\
         theorem inside_four : C.v = 4 := rfl\nend\n\
         theorem after_four : C.v = 4 := rfl\n\
         theorem after_one : C.v = 1 := rfl\n"
    ));
    assert!(accepted(&verdicts, "inside_one"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "inside_four"), "{verdicts:?}");
    assert!(accepted(&verdicts, "after_four"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "after_one"), "{verdicts:?}");
}

/// A top-level erase lasts for the rest of the file; re-adding appends
/// (Lean: 1, then 4); erasing an instance that is not in the state is Lean's
/// error ("'ib' does not have [instance] attribute").
#[test]
fn a_top_level_erase_lasts_and_a_re_addition_appends() {
    let verdicts = run_file(&format!(
        "{B}instance i4 : C := ⟨4⟩\n\
         attribute [-instance] i4\n\
         theorem erased_one : C.v = 1 := rfl\n\
         theorem erased_four : C.v = 4 := rfl\n\
         attribute [instance] i4\n\
         theorem readded_four : C.v = 4 := rfl\n\
         theorem readded_one : C.v = 1 := rfl\n\
         attribute [-instance] ib\n\
         attribute [-instance] ib\n"
    ));
    assert!(accepted(&verdicts, "erased_one"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "erased_four"), "{verdicts:?}");
    assert!(accepted(&verdicts, "readded_four"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "readded_one"), "{verdicts:?}");
    let not_an_instance = verdicts.iter().filter(|(_, verdict)| {
        verdict
            .as_ref()
            .err()
            .is_some_and(|e| e.contains("does not have [instance] attribute"))
    });
    assert_eq!(not_an_instance.count(), 1, "{verdicts:?}");
}

/// An erase does not reach an importer: Lean never exports it.
#[test]
fn an_erase_is_not_exported() {
    let verdicts = run_modules(&[
        B,
        "instance i4 : C := ⟨4⟩\nattribute [-instance] i4\n",
        "theorem four : C.v = 4 := rfl\ntheorem one : C.v = 1 := rfl\n",
    ]);
    assert!(accepted(&verdicts, "four"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "one"), "{verdicts:?}");
}

/// Re-adding a PRESENT instance with a new priority replaces it in place:
/// `instance (priority := high) h`, `instance i9`, `attribute [instance] h`
/// resolves to 9 (Lean: 9) — `h` keeps its place, at the default priority.
#[test]
fn an_in_place_priority_change_keeps_the_place() {
    let verdicts = run_file(&format!(
        "{B}instance (priority := high) h : C := ⟨8⟩\n\
         instance i9 : C := ⟨9⟩\n\
         attribute [instance] h\n\
         theorem eight : C.v = 8 := rfl\n\
         theorem nine : C.v = 9 := rfl\n"
    ));
    assert!(!accepted(&verdicts, "eight"), "{verdicts:?}");
    assert!(accepted(&verdicts, "nine"), "{verdicts:?}");
}

/// `attribute [local instance] i7` on a present low-priority instance
/// replaces it in place in the current scope at the default priority, where
/// it is the newest of the tier (Lean: 7).
#[test]
fn an_in_place_local_priority_change_keeps_the_place() {
    let verdicts = run_file(&format!(
        "{B}instance i4 : C := ⟨4⟩\n\
         instance (priority := low) i7 : C := ⟨7⟩\n\
         attribute [local instance] i7\n\
         theorem seven : C.v = 7 := rfl\n\
         theorem four : C.v = 4 := rfl\n"
    ));
    assert!(accepted(&verdicts, "seven"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "four"), "{verdicts:?}");
}

/// The fbbb586e0 regression (`erase_readd`, `er_same`): `attribute
/// [-instance] ib` then `attribute [instance] ib` leaves `ib` where it was,
/// behind the newer `ic` (Lean: 2); so does a `local` re-addition
/// (`er_local`, Lean: 2).
#[test]
fn an_erased_instance_re_added_keeps_its_place() {
    let verdicts = run_file(&format!(
        "{B}instance ic : C := ⟨2⟩\n\
         attribute [-instance] ib\n\
         attribute [instance] ib\n\
         theorem readded_two : C.v = 2 := rfl\n\
         theorem readded_one : C.v = 1 := rfl\n\
         attribute [-instance] ib\n\
         attribute [local instance] ib\n\
         theorem local_two : C.v = 2 := rfl\n\
         theorem local_one : C.v = 1 := rfl\n"
    ));
    assert!(accepted(&verdicts, "readded_two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "readded_one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "local_two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "local_one"), "{verdicts:?}");
}

/// `er_prio_low` / `er_prio`: an erased high-priority instance re-added at
/// the default priority falls behind the newer `ic` in its old place (Lean:
/// 2); re-added `high`, it is first again (Lean: 1).
#[test]
fn an_erased_instance_re_added_takes_the_new_priority_in_place() {
    let verdicts = run_file(
        "class C where\n  v : Nat\n\
         instance (priority := high) ib : C := ⟨1⟩\n\
         instance ic : C := ⟨2⟩\n\
         attribute [-instance] ib\n\
         attribute [instance] ib\n\
         theorem default_two : C.v = 2 := rfl\n\
         theorem default_one : C.v = 1 := rfl\n\
         attribute [-instance] ib\n\
         attribute [instance high] ib\n\
         theorem high_one : C.v = 1 := rfl\n\
         theorem high_two : C.v = 2 := rfl\n",
    );
    assert!(accepted(&verdicts, "default_two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "default_one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "high_one"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "high_two"), "{verdicts:?}");
}

/// `er_imp`: an imported instance erased and re-added keeps its imported
/// place (Lean: 2).
#[test]
fn an_imported_instance_erased_and_re_added_keeps_its_place() {
    let verdicts = run_modules(&[
        "class C where\n  v : Nat\ninstance ib : C := ⟨1⟩\ninstance ic : C := ⟨2⟩\n",
        "attribute [-instance] ib\n\
         attribute [instance] ib\n\
         theorem two : C.v = 2 := rfl\n\
         theorem one : C.v = 1 := rfl\n",
    ]);
    assert!(accepted(&verdicts, "two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "one"), "{verdicts:?}");
}

/// A `local instance` given a global entry later in its own module is in
/// place there (behind the newer `i4`: Lean 4), but an importer, which never
/// sees the local entry, has it pushed after `i4` (Lean: 3).
#[test]
fn a_local_instance_made_global_is_in_place_here_and_newest_in_an_importer() {
    let module = "local instance i3 : C := ⟨3⟩\n\
                  instance i4 : C := ⟨4⟩\n\
                  attribute [instance] i3\n";
    let here = run_modules(&[
        "class C where\n  v : Nat\n",
        &format!(
            "{module}theorem here_four : C.v = 4 := rfl\n\
             theorem here_three : C.v = 3 := rfl\n"
        ),
    ]);
    assert!(accepted(&here, "here_four"), "{here:?}");
    assert!(!accepted(&here, "here_three"), "{here:?}");
    let importer = run_modules(&[
        "class C where\n  v : Nat\n",
        module,
        "theorem there_three : C.v = 3 := rfl\ntheorem there_four : C.v = 4 := rfl\n",
    ]);
    assert!(accepted(&importer, "there_three"), "{importer:?}");
    assert!(!accepted(&importer, "there_four"), "{importer:?}");
}

/// Lean replays imported global entries in import order, each re-insertion
/// in place: `P: attribute [instance] ic` (a no-op there) after `Q:
/// attribute [instance 50] ic` puts `ic` back at 1000 (Lean: `import Q;
/// import P` gives 2), and before it leaves 50 (`import P; import Q` gives
/// 1).
#[test]
fn imported_re_insertions_replay_in_import_order() {
    let b = "class C where\n  v : Nat\ninstance ib : C := ⟨1⟩\ninstance ic : C := ⟨2⟩\n";
    let p = "attribute [instance] ic\n";
    let q = "attribute [instance 50] ic\n";
    let claims = "theorem one : C.v = 1 := rfl\ntheorem two : C.v = 2 := rfl\n";
    let p_then_q = run_modules(&[b, p, q, claims]);
    assert!(accepted(&p_then_q, "one"), "{p_then_q:?}");
    assert!(!accepted(&p_then_q, "two"), "{p_then_q:?}");
    let q_then_p = run_modules(&[b, q, p, claims]);
    assert!(accepted(&q_then_p, "two"), "{q_then_p:?}");
    assert!(!accepted(&q_then_p, "one"), "{q_then_p:?}");
}

/// A scoped entry for an instance that also has a global one re-inserts it
/// IN PLACE with the scoped entry's priority wherever the namespace is
/// active (Lean: 2 without `N`, 1 under `open N in`).
#[test]
fn a_scoped_entry_re_inserts_a_global_instance_in_place() {
    let verdicts = run_file(&format!(
        "{B}instance ic : C := ⟨2⟩\n\
         namespace N\nattribute [scoped instance 2000] _root_.ib\nend N\n\
         theorem outside_two : C.v = 2 := rfl\n\
         theorem outside_one : C.v = 1 := rfl\n\
         open N in\ntheorem inside_one : C.v = 1 := rfl\n\
         open N in\ntheorem inside_two : C.v = 2 := rfl\n"
    ));
    assert!(accepted(&verdicts, "outside_two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "outside_one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "inside_one"), "{verdicts:?}");
    assert!(refused_with(&verdicts, "inside_two", "= 2"), "{verdicts:?}");
}

/// `open N in cmd` is `section open N cmd end`: an erase or a `local` entry
/// inside it ends with it, a global entry does not (Lean: 2, 2, 5). Clean
/// used to apply the inner command's attributes after the `open … in` scope,
/// at the file level, and credited 1.
#[test]
fn an_open_in_command_scopes_the_instance_state() {
    let verdicts = run_file(&format!(
        "{B}instance ic : C := ⟨2⟩\n\
         open Nat in\nattribute [-instance] ic\n\
         theorem erase_two : C.v = 2 := rfl\n\
         theorem erase_one : C.v = 1 := rfl\n\
         set_option pp.all true in\nattribute [local instance] ib\n\
         theorem local_two : C.v = 2 := rfl\n\
         theorem local_one : C.v = 1 := rfl\n\
         def d5 : C := ⟨5⟩\n\
         open Nat in\nattribute [instance] d5\n\
         theorem global_five : C.v = 5 := rfl\n\
         theorem global_two : C.v = 2 := rfl\n"
    ));
    assert!(accepted(&verdicts, "erase_two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "erase_one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "local_two"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "local_one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "global_five"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "global_two"), "{verdicts:?}");
}

/// Lean's `resolveNamespace`: inside `namespace N`, `open N` means `N.N` —
/// a namespace the nested block registered although nothing is declared
/// directly in it — and activates its scoped entries (Lean: 16; Clean used
/// to open the root `N` and credit 1).
#[test]
fn open_inside_a_namespace_resolves_a_registered_nested_namespace() {
    let verdicts = run_file(&format!(
        "{B}namespace N\n\
         def i16 : C := ⟨16⟩\n\
         namespace N\nattribute [scoped instance high] _root_.N.i16\nend N\n\
         open N in\ntheorem sixteen : C.v = 16 := rfl\n\
         open N in\ntheorem one : C.v = 1 := rfl\n\
         end N\n"
    ));
    assert!(accepted(&verdicts, "sixteen"), "{verdicts:?}");
    assert!(refused_with(&verdicts, "one", "= 1"), "{verdicts:?}");
}

/// `attribute [local instance] c` on a fresh definition: in force until the
/// section ends (Lean: 5 inside, 1 after).
#[test]
fn a_local_instance_attribute_ends_with_its_section() {
    let verdicts = run_file(&format!(
        "{B}def c : C := ⟨5⟩\n\
         section\nattribute [local instance] c\n\
         theorem inside_five : C.v = 5 := rfl\n\
         theorem inside_one : C.v = 1 := rfl\nend\n\
         theorem after_one : C.v = 1 := rfl\n\
         theorem after_five : C.v = 5 := rfl\n"
    ));
    assert!(accepted(&verdicts, "inside_five"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "inside_one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "after_one"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "after_five"), "{verdicts:?}");
}

/// `attribute [scoped instance] _root_.c` inside `namespace N`, with `N`
/// opened at the top level: Lean adds it to every state where `N` is active,
/// the top level's included (Lean: 13). It used to be a parse error, and the
/// declarations after it were credited against a state without it.
#[test]
fn a_scoped_instance_attribute_parses_and_follows_activation() {
    let verdicts = run_file(&format!(
        "{B}namespace N\ndef nn : Nat := 0\nend N\n\
         instance i11 : C := ⟨11⟩\n\
         open N\n\
         def i13 : C := ⟨13⟩\n\
         namespace N\nattribute [scoped instance] _root_.i13\nend N\n\
         theorem thirteen : C.v = 13 := rfl\n\
         theorem eleven : C.v = 11 := rfl\n"
    ));
    assert!(accepted(&verdicts, "thirteen"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "eleven"), "{verdicts:?}");
}

/// Without an active `N`, the scoped attribute's instance is invisible after
/// `end N` (Lean: 11), and `open scoped N` activates it (Lean: 13).
#[test]
fn a_scoped_instance_attribute_is_invisible_until_activated() {
    let verdicts = run_file(&format!(
        "{B}instance i11 : C := ⟨11⟩\n\
         def i13 : C := ⟨13⟩\n\
         namespace N\nattribute [scoped instance] _root_.i13\nend N\n\
         theorem before_eleven : C.v = 11 := rfl\n\
         theorem before_thirteen : C.v = 13 := rfl\n\
         open scoped N\n\
         theorem after_thirteen : C.v = 13 := rfl\n\
         theorem after_eleven : C.v = 11 := rfl\n"
    ));
    assert!(accepted(&verdicts, "before_eleven"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "before_thirteen"), "{verdicts:?}");
    assert!(accepted(&verdicts, "after_thirteen"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "after_eleven"), "{verdicts:?}");
}

/// Named priorities in the `instance` attribute (`instance high`) parse; the
/// command used to be a parse error (Lean: 5 over the newer default `i6`).
#[test]
fn a_named_attribute_priority_parses() {
    let verdicts = run_file(&format!(
        "{B}def c : C := ⟨5⟩\n\
         attribute [instance high] c\n\
         instance i6 : C := ⟨6⟩\n\
         theorem five : C.v = 5 := rfl\n\
         theorem six : C.v = 6 := rfl\n"
    ));
    assert!(accepted(&verdicts, "five"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "six"), "{verdicts:?}");
}

/// A line-start `local instance` ends an attribute's target list and a
/// declaration's value (both used to swallow `local`: the attribute failed
/// with "target 'local' not found" and `⟨3⟩ local …` was an application).
#[test]
fn a_line_start_local_instance_starts_a_new_command() {
    let verdicts = run_file(&format!(
        "{B}def c : C := ⟨5⟩\n\
         attribute [instance] c\n\
         local instance (priority := low) i3 : C := ⟨3⟩\n\
         local instance (priority := low) i4 : C := ⟨4⟩\n\
         theorem five : C.v = 5 := rfl\n\
         theorem one : C.v = 1 := rfl\n"
    ));
    assert!(
        verdicts
            .iter()
            .all(|(name, verdict)| verdict.is_ok() || name == "one"),
        "{verdicts:?}"
    );
    assert!(accepted(&verdicts, "five"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "one"), "{verdicts:?}");
}
