// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A keyword may HEAD an `instance` declaration's name: `instance Prop.instCompl`.
//!
//! # The defect these fixtures pin
//!
//! Clean's lexer never joins dotted names, so `Prop.instCompl` arrives as
//! `[Prop][Dot][Ident]` and every declaration form has to stitch it back
//! together. `51dcb1193` taught `qualified_ident_impl` to accept a keyword head
//! (guarded on a byte-adjacent `.`), which fixed `def`, `theorem`, `abbrev`,
//! `axiom`, `structure`, `class` and `inductive` at once — but **not**
//! `instance`, because `instance` decides whether a name is present at all
//! before it parses one:
//!
//! ```text
//! let name = if let TokenKind::Ident(_) = self.current_kind() { … } else { None };
//! ```
//!
//! `instance` is the one form with an anonymous spelling (`instance : Compl Prop`),
//! so that look-ahead exists for a real reason — but on `Prop` it took the
//! anonymous branch, `optional_binders` stopped at a token it did not own, and
//! the declaration died at `expected Colon, got Prop` (Mathlib
//! `Order/Basic.lean:502`, `:1083`, `:1093`).
//!
//! Measured in `mathlib4` at `43ad0e9d2` on 2026-08-31: **28** `instance`
//! declarations across **14** files head their name with a keyword
//! (`Prop.instCompl`, `Prop.linearOrder`, `Type.enoughProjectives`, …).
//! In the pinned SRCELAB slice the three in `Order/Basic.lean` are the roots of
//! six `failed to synthesize instance` failures: `compl_lt`, `compl_le`,
//! `compl_gt`, `compl_ge` and `Ne.instIsEquiv_compl` want the `Compl Prop` that
//! line 502 declares, and `subrelation_iff_le` wants the `LE Prop` of line 1083.
//!
//! # What must NOT change
//!
//! A BARE keyword is still not a name. `instance Prop : C` must keep failing
//! rather than quietly declaring an instance named `Prop` — that is the
//! convenient approximation ("a keyword after `instance` heads a name"), and
//! [`test_bare_keyword_is_not_an_instance_name`] is the fixture that refuses
//! it. Both readings live in one place, [`Parser::keyword_name_head`], so the
//! look-ahead and the parse cannot drift apart.

use crate::{parse_file, SurfaceDecl, SurfaceName};

/// The parsed instances' names, in source order (`None` = anonymous).
fn instance_names(src: &str) -> Vec<Option<SurfaceName>> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("parses: {e:?}"));
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "parser recovery produced a raw declaration, so nothing below is a \
         real parse: {decls:#?}"
    );
    decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Instance { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// Mathlib `Order/Basic.lean:502`, verbatim but for the class body.
#[test]
fn test_keyword_headed_instance_name_parses() {
    assert_eq!(
        instance_names("instance Prop.instCompl : Compl Prop :=\n  ⟨Not⟩\n"),
        vec![Some(SurfaceName::generated_path("Prop.instCompl"))],
    );
}

/// Mathlib `Order/Basic.lean:1093` — the `where` spelling, not `:=`.
#[test]
fn test_keyword_headed_instance_name_parses_with_where() {
    assert_eq!(
        instance_names("instance Prop.partialOrder : PartialOrder Prop where\n  le_refl _ := id\n"),
        vec![Some(SurfaceName::generated_path("Prop.partialOrder"))],
    );
}

/// Mathlib `Data/Countable/Defs.lean:102`: the name follows a `(priority := …)`
/// option AND is followed by a binder, not a `:` — both look-aheads at once.
#[test]
fn test_keyword_headed_instance_name_after_priority_and_before_binders() {
    assert_eq!(
        instance_names(
            "instance (priority := 100) Prop.countable (p : Prop) : Countable p :=\n  c\n"
        ),
        vec![Some(SurfaceName::generated_path("Prop.countable"))],
    );
}

/// Mathlib `CategoryTheory/Adhesive/Basic.lean:422` — `Prop` is not the only
/// keyword that heads a real Mathlib instance name.
#[test]
fn test_type_headed_instance_name_parses() {
    assert_eq!(
        instance_names("instance Type.adhesive : Adhesive (Type u) :=\n  h\n"),
        vec![Some(SurfaceName::generated_path("Type.adhesive"))],
    );
}

/// A keyword deeper in the name was already accepted; it must stay accepted.
#[test]
fn test_keyword_suffix_instance_name_parses() {
    assert_eq!(
        instance_names("instance Foo.Prop.instCompl : Compl Prop :=\n  ⟨Not⟩\n"),
        vec![Some(SurfaceName::generated_path("Foo.Prop.instCompl"))],
    );
}

/// CONTROL: the ordinary named instance, which never broke.
#[test]
fn test_ident_headed_instance_name_still_parses() {
    assert_eq!(
        instance_names("instance Nat.instCompl : Compl Nat :=\n  ⟨id⟩\n"),
        vec![Some(SurfaceName::generated_path("Nat.instCompl"))],
    );
}

/// CONTROL: the anonymous instance — the reading the name look-ahead exists to
/// protect. `instance : LE (α × β) where …` is Mathlib `Order/Basic.lean:869`.
#[test]
fn test_anonymous_instance_still_has_no_name() {
    assert_eq!(
        instance_names("instance : LE (Prod a b) where\n  le p q := True\n"),
        vec![None],
    );
}

/// CONTROL: an anonymous instance whose binders come first still has no name.
#[test]
fn test_anonymous_instance_with_binders_still_has_no_name() {
    assert_eq!(
        instance_names("instance [Foo a] : Compl a :=\n  ⟨id⟩\n"),
        vec![None],
    );
}

/// THE approximation fixture. A bare keyword is NOT a name: `Prop` here is a
/// type, and the declaration is malformed in Lean too. Accepting it would mint
/// an instance named `Prop` out of an anonymous instance's type.
#[test]
fn test_bare_keyword_is_not_an_instance_name() {
    let decls = parse_file("instance Prop : Compl Prop :=\n  ⟨Not⟩\n").expect("recovers");
    let named: Vec<_> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Instance { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    assert!(
        !named.contains(&Some(SurfaceName::generated_path("Prop"))),
        "a bare keyword must not become an instance NAME: {decls:#?}"
    );
}

/// The same rule at one remove: a keyword separated from its dot by a space is
/// not a name head either, so this is the anonymous reading plus a type, not
/// `instance Prop.instCompl`.
#[test]
fn test_keyword_not_adjacent_to_dot_is_not_an_instance_name() {
    let decls =
        parse_file("instance Prop .instCompl : Compl Prop :=\n  ⟨Not⟩\n").expect("recovers");
    let named: Vec<_> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Instance { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    assert!(
        !named.contains(&Some(SurfaceName::generated_path("Prop.instCompl"))),
        "`Prop .instCompl` is two tokens, not one name: {decls:#?}"
    );
}

#[test]
fn typed_quoted_keyword_head_and_quoted_dotted_leaf_remain_distinct() {
    let quoted = instance_names("instance «Prop.instCompl» : Compl Prop := ⟨Not⟩\n");
    let qualified = instance_names("instance Prop.instCompl : Compl Prop := ⟨Not⟩\n");
    let [Some(quoted)] = quoted.as_slice() else {
        panic!("quoted source name absent");
    };
    let [Some(qualified)] = qualified.as_slice() else {
        panic!("qualified source name absent");
    };
    assert!(quoted.same_syntax(&SurfaceName::component("Prop.instCompl", true)));
    assert_ne!(quoted.name(), qualified.name());
    let bare = instance_names("instance «Prop» : Compl Prop := ⟨Not⟩\n");
    let [Some(bare)] = bare.as_slice() else {
        panic!("quoted keyword is an ordinary name");
    };
    assert!(bare.same_syntax(&SurfaceName::component("Prop", true)));
}
