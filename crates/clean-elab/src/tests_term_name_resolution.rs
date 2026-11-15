// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How a TERM identifier resolves, Lean 4.8.0's way (`resolveGlobalName`):
//! an atomic name never reaches a `protected` declaration through a namespace
//! prefix; the root stage (root constant, `open` declarations, aliases) is ONE
//! candidate set, and more than one distinct candidate is ambiguous; another
//! module's `private` declaration is unreachable, dot notation included.
//! Round-25 verification of 100c3ccca found each of these credited with a
//! value Lean rejects. Every expectation was measured on Lean 4.8.0
//! (2026-09-26).

use crate::test_support::file_verdicts::{run_file, run_modules, run_modules_unnamed, verdict_of};

fn accepted(verdicts: &[(String, Result<(), String>)], name: &str) -> bool {
    verdict_of(verdicts, name).is_ok()
}

fn ambiguous(verdicts: &[(String, Result<(), String>)], name: &str) -> bool {
    verdict_of(verdicts, name)
        .as_ref()
        .err()
        .is_some_and(|e| e.contains("ambiguous"))
}

/// Inside `namespace N`, a bare `w` is the ROOT `w` when `N.w` is protected
/// (Lean: `w = 1` holds; round-25 `protin_3` credited `w = 3`).
#[test]
fn a_protected_namespace_member_is_not_reached_by_an_atomic_name() {
    let verdicts = run_file(
        "def w : Nat := 1\n\
         namespace N\n\
         protected def w : Nat := 3\n\
         theorem is_one : w = 1 := rfl\n\
         theorem is_three : w = 3 := rfl\n\
         theorem qualified : N.w = 3 := rfl\n\
         end N\n",
    );
    assert!(accepted(&verdicts, "N.is_one"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "N.is_three"), "{verdicts:?}");
    assert!(accepted(&verdicts, "N.qualified"), "{verdicts:?}");
}

/// A root `w` and an `open N` member `N.w` are two interpretations: Lean
/// reports "ambiguous, possible interpretations" (Clean used to take `N.w`).
#[test]
fn a_root_constant_and_an_opened_member_are_ambiguous() {
    let verdicts = run_file(
        "def w : Nat := 2\n\
         namespace N\ndef w : Nat := 3\nend N\n\
         open N\n\
         theorem t : w = 3 := rfl\n",
    );
    assert!(ambiguous(&verdicts, "t"), "{verdicts:?}");
}

/// Two opened namespaces with the same member are ambiguous too (Lean
/// 4.8.0, even when the two have different types).
#[test]
fn two_opened_members_are_ambiguous() {
    let verdicts = run_file(
        "namespace A\ndef x : Nat := 2\nend A\n\
         namespace B\ndef x : Nat := 3\nend B\n\
         open A B\n\
         theorem t : x = 3 := rfl\n",
    );
    assert!(ambiguous(&verdicts, "t"), "{verdicts:?}");
}

/// `open N (w)` names even a protected `N.w`, which is then ambiguous with a
/// root `w` (round-25 `protexpl_3`: Clean took `N.w`).
#[test]
fn an_explicit_open_of_a_protected_member_is_ambiguous_with_the_root() {
    let verdicts = run_modules(&[
        "def w : Nat := 2\nnamespace N\nprotected def w : Nat := 3\nend N\n",
        "open N (w)\ntheorem t : w = 3 := rfl\n",
    ]);
    assert!(ambiguous(&verdicts, "t"), "{verdicts:?}");
}

/// One interpretation reached two ways is not an ambiguity: an `export`ed
/// alias and the opened member it names.
#[test]
fn one_constant_reached_twice_is_not_ambiguous() {
    let verdicts = run_file(
        "namespace N\ndef w : Nat := 3\nend N\n\
         export N (w)\n\
         open N\n\
         theorem t : w = 3 := rfl\n",
    );
    assert!(accepted(&verdicts, "t"), "{verdicts:?}");
}

/// Another module's `private def Nat.three` is no target for dot notation
/// (round-25 `privdot_3`: `(0 : Nat).three = 3` was credited).
#[test]
fn an_imported_private_declaration_is_not_a_dot_notation_target() {
    let verdicts = run_modules(&[
        "private def Nat.three (n : Nat) : Nat := 3\n",
        "theorem t : (0 : Nat).three = 3 := rfl\n",
    ]);
    assert!(!accepted(&verdicts, "t"), "{verdicts:?}");
}

/// [`an_imported_private_declaration_is_not_a_dot_notation_target`] with no
/// module names: the plain `Nat.three` is kept from the importer by the
/// foreign-private filter alone.
#[test]
fn an_imported_private_declaration_is_not_a_dot_notation_target_unnamed() {
    let verdicts = run_modules_unnamed(&[
        "private def Nat.three (n : Nat) : Nat := 3\n",
        "theorem t : (0 : Nat).three = 3 := rfl\n",
    ]);
    assert!(!accepted(&verdicts, "t"), "{verdicts:?}");
}

/// A definition whose value is another constant is a constant of its own to
/// Lean: `def w := N.w` and `N.w` under `open N` are two interpretations
/// (round-25 verification of fbbb586e0, `dedup_abbrev`; Lean reports
/// "ambiguous, possible interpretations"). Clean read the root `w` through
/// its value as `N.w` and credited `w = 3`.
#[test]
fn a_user_alias_definition_is_its_own_interpretation() {
    let verdicts = run_modules(&[
        "namespace N\ndef w : Nat := 3\nend N\ndef w := N.w\n",
        "open N\ntheorem t : w = 3 := rfl\n",
    ]);
    assert!(ambiguous(&verdicts, "t"), "{verdicts:?}");
}

/// The sharpest form (`dedup_mynat`): `w : MyNat := N.w` with `N.w : Nat`
/// was merged with `N.w`, so `w + w` used `Nat`'s addition where the root
/// reading uses `MyNat`'s multiplication; Lean rejects both readings as
/// ambiguous under `open N`.
#[test]
fn an_alias_definition_of_another_type_is_not_merged() {
    let verdicts = run_modules(&[
        "namespace N\ndef w : Nat := 3\nend N\n\
         def MyNat := Nat\n\
         instance : Add MyNat := ⟨fun a b => Nat.mul a b⟩\n\
         def w : MyNat := N.w\n",
        "open N\ntheorem six : (w + w : Nat) = 6 := rfl\n",
    ]);
    assert!(!accepted(&verdicts, "six"), "{verdicts:?}");
}

/// Lean's `export` adds its alias to the ENVIRONMENT, which an importer
/// replays: with a root `x` and `export N (x)` in B, `x` is ambiguous in B's
/// importer as in B (round-25 `export_root`; Clean credited `x = 1` in the
/// importer).
#[test]
fn an_export_alias_reaches_an_importer() {
    let verdicts = run_modules(&[
        "def x : Nat := 1\nnamespace N\ndef x : Nat := 2\nend N\nexport N (x)\n",
        "theorem one : x = 1 := rfl\ntheorem two : x = 2 := rfl\n",
    ]);
    assert!(ambiguous(&verdicts, "one"), "{verdicts:?}");
    assert!(ambiguous(&verdicts, "two"), "{verdicts:?}");
}

/// An `export` made inside a namespace is an alias `K.x` an `open K`
/// reaches (Lean's `resolveQualifiedName` takes the aliases of `K ++ x`): with
/// a root `x` as well, `x` is ambiguous and `K.x` is `N.x` (round-25
/// `export_ns`; Clean credited `x = 1` and refused `K.x = 2`).
#[test]
fn an_export_inside_a_namespace_is_reached_through_open() {
    let verdicts = run_modules(&[
        "namespace N\ndef x : Nat := 2\nend N\n\
         namespace K\nexport N (x)\nend K\n\
         def x : Nat := 1\n",
        "open K\n\
         theorem one : x = 1 := rfl\n\
         theorem k_two : K.x = 2 := rfl\n",
    ]);
    assert!(ambiguous(&verdicts, "one"), "{verdicts:?}");
    assert!(accepted(&verdicts, "k_two"), "{verdicts:?}");
}

/// Lean keeps every open declaration and alias: a later `open` or `export`
/// giving a short name another target does not shadow the earlier one, the
/// name is ambiguous (measured on Lean 4.8.0; Clean's alias table kept only
/// the latest and credited it).
#[test]
fn a_later_open_or_export_does_not_shadow_an_earlier_one() {
    let explicit_then_export = run_file(
        "def A.x : Nat := 2\ndef K.x : Nat := 5\n\
         open A (x)\nexport K (x)\n\
         theorem five : x = 5 := rfl\ntheorem two : x = 2 := rfl\n",
    );
    assert!(
        ambiguous(&explicit_then_export, "five"),
        "{explicit_then_export:?}"
    );
    assert!(
        ambiguous(&explicit_then_export, "two"),
        "{explicit_then_export:?}"
    );
    let two_renamings = run_file(
        "def N.x : Nat := 1\ndef K.x : Nat := 4\n\
         open K renaming x → z\nopen N renaming x → z\n\
         theorem four : z = 4 := rfl\ntheorem one : z = 1 := rfl\n",
    );
    assert!(ambiguous(&two_renamings, "four"), "{two_renamings:?}");
    assert!(ambiguous(&two_renamings, "one"), "{two_renamings:?}");
}

/// At one namespace prefix, the declaration and the aliases of that name are
/// one candidate set (`resolveQualifiedName`): inside `namespace A`, with
/// `def A.x` and `export N.M (x)` there, `x` is ambiguous, while the dotted
/// `A.x` is the declaration (Lean 4.8.0; Clean returned the declaration for
/// `x`).
#[test]
fn a_declaration_and_an_alias_at_one_prefix_are_ambiguous() {
    let verdicts = run_file(
        "def A.x : Nat := 2\ndef N.M.x : Nat := 4\n\
         namespace A\nexport N.M (x)\n\
         theorem two : x = 2 := rfl\ntheorem four : x = 4 := rfl\n\
         theorem dotted : A.x = 2 := rfl\nend A\n",
    );
    assert!(ambiguous(&verdicts, "two"), "{verdicts:?}");
    assert!(ambiguous(&verdicts, "four"), "{verdicts:?}");
    assert!(accepted(&verdicts, "dotted"), "{verdicts:?}");
}

/// A dotted name reaches an alias at a namespace prefix: inside `namespace
/// K.K` with `export A (y)` there, `K.y` is `K.K.y`, the alias of `A.y`
/// (Lean 4.8.0: 5; Clean read the root `K.y` and credited 1).
#[test]
fn a_dotted_name_reaches_an_alias_at_a_namespace_prefix() {
    let verdicts = run_file(
        "def K.y : Nat := 1\ndef A.y : Nat := 5\n\
         namespace K\nnamespace K\nexport A (y)\n\
         theorem five : K.y = 5 := rfl\ntheorem one : K.y = 1 := rfl\n\
         end K\nend K\n",
    );
    assert!(accepted(&verdicts, "five"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "one"), "{verdicts:?}");
}

/// A dotted name that exists as written wins over an alias of the same name
/// (`resolveExact`): `def K.x := 3` beside `namespace K; export N.M (x)`
/// gives `K.x = 3` (Lean 4.8.0; Clean read the alias and credited 1).
#[test]
fn a_dotted_name_that_exists_wins_over_an_alias() {
    let verdicts = run_file(
        "def N.M.x : Nat := 1\ndef K.x : Nat := 3\n\
         namespace K\nexport N.M (x)\nend K\n\
         theorem three : K.x = 3 := rfl\ntheorem one : K.x = 1 := rfl\n",
    );
    assert!(accepted(&verdicts, "three"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "one"), "{verdicts:?}");
}

/// Opens made inside a scope end with it, however often they repeat the same
/// alias: `namespace N; open N; open N; end N` leaves no `x` (Lean 4.8.0:
/// `x = 3` is refused; Clean undid the second open's overwrite after the
/// first open's addition and kept `x ↦ N.x`).
#[test]
fn a_repeated_open_ends_with_its_scope() {
    let verdicts = run_file(
        "def N.x : Nat := 3\n\
         namespace N\nopen N\nopen N\nend N\n\
         theorem t : x = 3 := rfl\n",
    );
    assert!(!accepted(&verdicts, "t"), "{verdicts:?}");
}

/// Each `open` is its own declaration to Lean: `open N hiding x` hides `x`
/// only from itself, so after `open N` the name stays reachable (Lean: `x =
/// 3` holds), and an `open N hiding x` in an ended section hides nothing
/// (with `open M` too, `x` is ambiguous). Clean merged the hiding lists and
/// kept them past the section.
#[test]
fn a_hiding_open_does_not_hide_from_another_open() {
    let still_reached =
        run_file("def N.x : Nat := 3\nopen N\nopen N hiding x\ntheorem t : x = 3 := rfl\n");
    assert!(accepted(&still_reached, "t"), "{still_reached:?}");
    let ended = run_file(
        "def N.x : Nat := 3\ndef M.x : Nat := 4\nopen N\nopen M\n\
         section\nopen N hiding x\nend\n\
         theorem t : x = 4 := rfl\n",
    );
    assert!(ambiguous(&ended, "t"), "{ended:?}");
}

/// `export K (y)` resolves `K.y` as a constant name, so an alias `K.y`
/// (made by `namespace K; export N.M (y)`) gives `y ↦ N.M.y`, ambiguous with
/// a root `y` (Lean 4.8.0; Clean refused the export as an unknown member).
#[test]
fn an_export_of_an_alias_names_its_target() {
    let verdicts = run_file(
        "def N.M.y : Nat := 2\n\
         namespace K\nexport N.M (y)\nend K\n\
         def y : Nat := 3\n\
         export K (y)\n\
         theorem three : y = 3 := rfl\ntheorem two : y = 2 := rfl\n",
    );
    assert!(ambiguous(&verdicts, "three"), "{verdicts:?}");
    assert!(ambiguous(&verdicts, "two"), "{verdicts:?}");
}

/// This module's `private` declarations are accessible everywhere in it, not
/// only inside their own namespace (Lean 4.8.0 accepts every theorem here,
/// measured 2026-09-27). 403ef3be6 routed structure-method dot notation
/// through the accessibility check, which then refused `(S.mk 1).g`; plain
/// `T.g 2` and `U.k 2` outside their namespaces were refused on every build.
#[test]
fn this_modules_private_declarations_are_accessible_throughout_it() {
    let verdicts = run_file(
        "structure S where\n  a : Nat\n\
         private def S.g (s : S) : Nat := s.a + 1\n\
         theorem t1 : (S.mk 1).g = 2 := rfl\n\
         theorem t2 : S.g (S.mk 1) = 2 := rfl\n\
         private def T.g (n : Nat) : Nat := n\n\
         theorem t3 : T.g 2 = 2 := rfl\n\
         namespace U\nprivate def k (n : Nat) : Nat := n\nend U\n\
         theorem t4 : U.k 2 = 2 := rfl\n\
         def x (s : S) := s.g\n\
         theorem t5 : x (S.mk 1) = 2 := rfl\n",
    );
    for name in ["t1", "t2", "t3", "t4", "t5"] {
        assert!(accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
}

/// An imported module's `private def S.g` is never credited to `(S.mk 1).g`
/// here (Lean: the importer's own `S.g` gives 8). Since G21 brick B2
/// (`designs/2026-10-08-private-name-mangling.md`) the imported private def
/// is `_private.M0.0.S.g`, so the importer's public `def S.g` is a distinct
/// constant and `is_eight` holds, as Lean 4.8.0 accepts it; the false value
/// base and 100c3ccca credited (2) stays refused.
#[test]
fn an_imported_private_method_is_never_credited_to_the_importer() {
    let verdicts = run_modules(&[
        "structure S where\n  a : Nat\n\
         private def S.g (s : S) : Nat := s.a + 1\n",
        "def S.g (s : S) : Nat := s.a + 7\n\
         theorem is_eight : (S.mk 1).g = 8 := rfl\n\
         theorem is_two : (S.mk 1).g = 2 := rfl\n",
    ]);
    assert!(accepted(&verdicts, "is_eight"), "{verdicts:?}");
    assert!(!accepted(&verdicts, "is_two"), "{verdicts:?}");
}

/// [`an_imported_private_method_is_never_credited_to_the_importer`] with no
/// module names (the regime before G21 B2): the private `S.g` stays plain,
/// so the importer's `def S.g` is refused as a duplicate and `is_eight` with
/// it (a known gap of the unnamed regime), and the foreign-private filter
/// keeps the false value (2) refused.
#[test]
fn an_imported_private_method_is_never_credited_to_the_importer_unnamed() {
    let verdicts = run_modules_unnamed(&[
        "structure S where\n  a : Nat\n\
         private def S.g (s : S) : Nat := s.a + 1\n",
        "def S.g (s : S) : Nat := s.a + 7\n\
         theorem is_eight : (S.mk 1).g = 8 := rfl\n\
         theorem is_two : (S.mk 1).g = 2 := rfl\n",
    ]);
    assert!(!accepted(&verdicts, "is_two"), "{verdicts:?}");
}

/// Lean's overload resolution (`ElabCtx::elab_overloaded`): an identifier
/// with two root-stage candidates is the one that elaborates in context, and
/// stays ambiguous when both do. Measured on Lean 4.8.0 (2026-09-27): `f 1 =
/// 102` holds; `g` is "ambiguous, possible interpretations".
#[test]
fn an_ambiguous_identifier_is_the_one_candidate_that_elaborates() {
    let verdicts = run_file(
        "namespace MX\ndef outParam (n : Nat) : Nat := n + 100\nend MX\n\
         export MX (outParam)\n\
         def f (a : Nat) : Nat := outParam a + 1\n\
         theorem is_102 : f 1 = 102 := rfl\n\
         namespace A\ndef k : Nat := 10\nend A\n\
         def k : Nat := 30\n\
         open A\n\
         def g : Nat := k\n",
    );
    assert!(accepted(&verdicts, "is_102"), "{verdicts:?}");
    assert!(ambiguous(&verdicts, "g"), "{verdicts:?}");
}
