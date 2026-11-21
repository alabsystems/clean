// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The optional universe level of `Type` / `Sort` follows Lean 4's guard
//! (`Lean/Parser/Term.lean:135-139`, v4.30.0-rc2):
//!
//! ```text
//! "Type" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
//! ```
//!
//! Clean read a level whenever a level-shaped token followed, so in
//!
//! ```text
//! structure D1 where
//!   Prov : Type
//!   n : Nat
//! ```
//!
//! the next field's name `n` became `Type n` and the rest of the block a
//! parser-recovery raw declaration (`Colon  Nat`). Lean refuses that level by
//! `checkColGt`: the field block (`structFields := manyIndent …`) saves the
//! first field's column and `n` is not right of it. The same holds for every
//! block Lean parses with `manyIndent` / `sepByIndent` — instance and `def`
//! `where` fields, `{ … }` structure instances, `where` auxiliary
//! declarations — while a parenthesised group or an explicit, implicit or
//! instance binder group (`withoutPosition`) and a command with no saved
//! position still read a level on the next line. A Lean keyword is never a
//! level.

use super::Parser;
use crate::{
    CodataBody, LevelExpr, SurfaceDecl, SurfaceExpr, SurfaceField, SurfaceFieldAssign, UniverseExpr,
};

/// Parse a whole file and require that no declaration fell to parser
/// recovery.
fn parse_without_recovery(src: &str) -> Vec<SurfaceDecl> {
    let decls = Parser::parse_file(src).unwrap_or_else(|e| panic!("must parse, got {e:?}\n{src}"));
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "no declaration may fall to parser recovery; got {decls:?}\n{src}"
    );
    decls
}

fn names(fields: &[SurfaceField]) -> Vec<String> {
    fields.iter().map(|f| f.name.to_string()).collect()
}

fn assign_names(fields: &[SurfaceFieldAssign]) -> Vec<String> {
    fields.iter().map(|f| f.name.to_string()).collect()
}

fn structure_fields(decl: &SurfaceDecl) -> &[SurfaceField] {
    match decl {
        SurfaceDecl::Structure { fields, .. } | SurfaceDecl::Class { fields, .. } => fields,
        other => panic!("expected a structure or class, got {other:?}"),
    }
}

fn is_bare_type(e: &SurfaceExpr) -> bool {
    matches!(e, SurfaceExpr::Universe(_, UniverseExpr::Type))
}

fn is_param(level: &LevelExpr, name: &str) -> bool {
    matches!(level, LevelExpr::Param(p) if p.to_string() == name)
}

fn type_level(e: &SurfaceExpr) -> Option<&LevelExpr> {
    match e {
        SurfaceExpr::Universe(_, UniverseExpr::TypeLevel(level)) => Some(level),
        _ => None,
    }
}

fn sort_level(e: &SurfaceExpr) -> Option<&LevelExpr> {
    match e {
        SurfaceExpr::Universe(_, UniverseExpr::Sort(level)) => Some(level),
        _ => None,
    }
}

// ─── The reported shapes ────────────────────────────────────────────────────

#[test]
fn type_field_then_next_field_is_two_fields() {
    let decls = parse_without_recovery("structure D1 where\n  Prov : Type\n  n : Nat\n");
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["Prov", "n"]);
    assert!(
        is_bare_type(&fields[0].ty),
        "`Prov : Type` keeps a bare `Type`: {:?}",
        fields[0].ty
    );
}

#[test]
fn class_type_field_then_function_field_is_two_fields() {
    let decls = parse_without_recovery(
        "class MemC (M : Type) where\n  Prov : Type\n  alloc : M → Option (M × Prov)\n",
    );
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["Prov", "alloc"]);
    assert!(is_bare_type(&fields[0].ty), "{:?}", fields[0].ty);
    assert!(
        matches!(fields[1].ty, SurfaceExpr::Arrow(..)),
        "{:?}",
        fields[1].ty
    );
}

#[test]
fn several_type_fields_then_function_fields() {
    let decls = parse_without_recovery(
        "structure MemDict where\n  Prov : Type\n  FrameExtra : Type\n  St : Type\n  \
         newCall : FrameExtra\n  allocate : St → Nat → Option (St × Prov)\n",
    );
    let fields = structure_fields(&decls[0]);
    assert_eq!(
        names(fields),
        ["Prov", "FrameExtra", "St", "newCall", "allocate"]
    );
    for field in &fields[..3] {
        assert!(is_bare_type(&field.ty), "{} : {:?}", field.name, field.ty);
    }
}

// ─── Near neighbours that share the cause ───────────────────────────────────

#[test]
fn bare_sort_field_then_next_field() {
    let decls = parse_without_recovery("structure S where\n  A : Sort\n  m : Nat\n");
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["A", "m"]);
    assert!(
        matches!(
            fields[0].ty,
            SurfaceExpr::Universe(_, UniverseExpr::SortImplicit)
        ),
        "{:?}",
        fields[0].ty
    );
}

#[test]
fn type_as_arrow_codomain_then_next_field() {
    let decls = parse_without_recovery("structure S where\n  F : Nat → Type\n  m : Nat\n");
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["F", "m"]);
    assert!(
        matches!(&fields[0].ty, SurfaceExpr::Arrow(_, _, cod) if is_bare_type(cod)),
        "{:?}",
        fields[0].ty
    );
}

#[test]
fn type_field_with_default_then_next_field() {
    let decls = parse_without_recovery("structure S where\n  A : Type 1 := Type\n  m : Nat\n");
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["A", "m"]);
    assert!(
        fields[0].default.as_ref().is_some_and(is_bare_type),
        "{:?}",
        fields[0].default
    );
}

#[test]
fn instance_where_type_value_then_next_field() {
    let decls = parse_without_recovery(
        "class C (α : Type) where\n  T : Type 1\n  n : Nat\n\n\
         instance : C Nat where\n  T := Type\n  n := 3\n",
    );
    match &decls[1] {
        SurfaceDecl::Instance { fields, .. } => {
            assert_eq!(assign_names(fields), ["T", "n"]);
            assert!(is_bare_type(&fields[0].val), "{:?}", fields[0].val);
        }
        other => panic!("expected an instance, got {other:?}"),
    }
}

#[test]
fn def_where_struct_instance_type_value_then_next_field() {
    let decls = parse_without_recovery(
        "structure S where\n  T : Type 1\n  n : Nat\n\n\
         def s : S where\n  T := Type\n  n := 3\n",
    );
    match &decls[1] {
        SurfaceDecl::Def { val, .. } => match val.as_ref() {
            SurfaceExpr::StructLit { fields, .. } => {
                assert_eq!(assign_names(fields), ["T", "n"]);
                assert!(is_bare_type(&fields[0].val), "{:?}", fields[0].val);
            }
            other => panic!("expected a structure instance, got {other:?}"),
        },
        other => panic!("expected a def, got {other:?}"),
    }
}

#[test]
fn brace_struct_instance_type_value_then_next_field() {
    let decls = parse_without_recovery(
        "structure S where\n  T : Type 1\n  n : Nat\n\n\
         def s : S := { T := Type\n               n := 4 }\n",
    );
    match &decls[1] {
        SurfaceDecl::Def { val, .. } => match val.as_ref() {
            SurfaceExpr::StructLit { fields, .. } => {
                assert_eq!(assign_names(fields), ["T", "n"]);
                assert!(is_bare_type(&fields[0].val), "{:?}", fields[0].val);
            }
            other => panic!("expected a structure instance, got {other:?}"),
        },
        other => panic!("expected a def, got {other:?}"),
    }
}

#[test]
fn codata_record_type_field_then_next_field() {
    let decls = parse_without_recovery("codata R where\n  T : Type\n  n : Nat\n");
    match &decls[0] {
        SurfaceDecl::Codata {
            body: CodataBody::Record(fields),
            ..
        } => {
            assert_eq!(names(fields), ["T", "n"]);
            assert!(is_bare_type(&fields[0].ty), "{:?}", fields[0].ty);
        }
        other => panic!("expected a codata record, got {other:?}"),
    }
}

// ─── Levels Lean still reads ────────────────────────────────────────────────

#[test]
fn same_line_levels_still_parse() {
    let decls = parse_without_recovery(
        "structure S where\n  A : Type u\n  B : Sort (u+1)\n  C : Type (max u v)\n  m : Nat\n",
    );
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["A", "B", "C", "m"]);
    assert!(
        type_level(&fields[0].ty).is_some_and(|l| is_param(l, "u")),
        "{:?}",
        fields[0].ty
    );
    assert!(
        sort_level(&fields[1].ty)
            .is_some_and(|l| matches!(l, LevelExpr::Succ(inner) if is_param(inner, "u"))),
        "{:?}",
        fields[1].ty
    );
    assert!(
        type_level(&fields[2].ty).is_some_and(|l| matches!(l, LevelExpr::Max(..))),
        "{:?}",
        fields[2].ty
    );
}

/// `checkColGt` compares columns, not lines: a level on a continuation line
/// indented PAST the field column is still the level.
#[test]
fn level_on_a_more_indented_next_line_is_still_the_level() {
    let decls = parse_without_recovery("structure S where\n  A : Type\n    u\n  m : Nat\n");
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["A", "m"]);
    assert!(
        type_level(&fields[0].ty).is_some_and(|l| is_param(l, "u")),
        "{:?}",
        fields[0].ty
    );
}

/// `structExplicitBinder` parses its contents `withoutPosition`, so inside
/// the parentheses a next-line level at the field column is still the level.
#[test]
fn parenthesised_field_group_has_no_saved_position() {
    let decls = parse_without_recovery("structure S where\n  (A : Type\n  u)\n  m : Nat\n");
    let fields = structure_fields(&decls[0]);
    assert_eq!(names(fields), ["A", "m"]);
    assert!(
        type_level(&fields[0].ty).is_some_and(|l| is_param(l, "u")),
        "{:?}",
        fields[0].ty
    );
}

/// With no saved position `checkColGt` passes, so a bare term reads a level
/// from the next line exactly as Lean does.
#[test]
fn no_saved_position_reads_a_next_line_level() {
    let expr = Parser::parse_expr("Type\nu").expect("should parse");
    assert!(
        type_level(&expr).is_some_and(|l| is_param(l, "u")),
        "{expr:?}"
    );
    let expr = Parser::parse_expr("Sort\nu").expect("should parse");
    assert!(
        sort_level(&expr).is_some_and(|l| is_param(l, "u")),
        "{expr:?}"
    );
}

// ─── The other two guards ───────────────────────────────────────────────────

/// `checkPrec leadPrec`: an application argument is parsed above `leadPrec`,
/// so `Sort` there is atomic, as `Type` already was.
#[test]
fn sort_in_argument_position_is_atomic() {
    let expr = Parser::parse_expr("g Sort u v").expect("should parse");
    match &expr {
        SurfaceExpr::App(_, _, args) => {
            assert_eq!(
                args.len(),
                3,
                "`Sort`, `u`, `v` are three arguments: {expr:?}"
            );
            assert!(
                matches!(
                    args[0].expr,
                    SurfaceExpr::Universe(_, UniverseExpr::SortImplicit)
                ),
                "{expr:?}"
            );
        }
        other => panic!("expected an application, got {other:?}"),
    }
    let expr = Parser::parse_expr("g (Sort u) v").expect("should parse");
    match &expr {
        SurfaceExpr::App(_, _, args) => {
            assert_eq!(args.len(), 2, "{expr:?}");
            let SurfaceExpr::Paren(_, inner) = &args[0].expr else {
                panic!("expected the parenthesised sort, got {expr:?}");
            };
            assert!(
                sort_level(inner).is_some_and(|l| is_param(l, "u")),
                "{expr:?}"
            );
        }
        other => panic!("expected an application, got {other:?}"),
    }
}

/// `checkWsBefore`: a level glued to the keyword is not its level.
#[test]
fn level_glued_to_the_keyword_is_not_a_level() {
    for src in ["Type(u)", "Sort(u)"] {
        let expr = Parser::parse_expr(src).expect("should parse");
        assert!(
            type_level(&expr).is_none() && sort_level(&expr).is_none(),
            "`{src}` must not read a level: {expr:?}"
        );
    }
    let expr = Parser::parse_expr("Type (u)").expect("should parse");
    assert!(
        type_level(&expr).is_some_and(|l| is_param(l, "u")),
        "{expr:?}"
    );
}

// ─── `where` auxiliary declarations save a position too ────────────────────
//
// `whereDecls := "where" >> sepByIndent (ppGroup letRecDecl) "; " …`
// (`Lean/Parser/Term.lean:701-702`): the first declaration's column is saved,
// so the next declaration's name is never a level of a `Type`- or
// `Sort`-valued body. Each source below is accepted by Lean 4.30.0-rc2.

fn where_decls(decl: &SurfaceDecl) -> &[crate::WhereLocalDef] {
    match decl {
        SurfaceDecl::Def { where_decls, .. } | SurfaceDecl::Theorem { where_decls, .. } => {
            where_decls
        }
        other => panic!("expected a def or theorem, got {other:?}"),
    }
}

fn where_names(decl: &SurfaceDecl) -> Vec<String> {
    where_decls(decl)
        .iter()
        .map(|d| d.name.to_string())
        .collect()
}

#[test]
fn where_decl_type_value_then_next_decl() {
    let decls = parse_without_recovery("def g : Nat := k\nwhere\n  T := Type\n  k := 3\n");
    assert_eq!(where_names(&decls[0]), ["T", "k"]);
    let body = &where_decls(&decls[0])[0].body;
    assert!(
        is_bare_type(body),
        "`T := Type` keeps a bare `Type`: {body:?}"
    );
}

#[test]
fn where_decl_typed_type_value_then_next_decl() {
    let decls = parse_without_recovery(
        "def foo : Nat := bar\nwhere\n  T : Type 1 := Type\n  bar : Nat := 0\n",
    );
    assert_eq!(where_names(&decls[0]), ["T", "bar"]);
    assert!(
        is_bare_type(&where_decls(&decls[0])[0].body),
        "{:?}",
        where_decls(&decls[0])[0].body
    );
}

#[test]
fn where_decl_sort_value_then_next_decl() {
    let decls = parse_without_recovery(
        "def g : Nat := k\nwhere\n  S : Type := Sort 0 → Nat\n  T := Sort\n  k := 3\n",
    );
    assert_eq!(where_names(&decls[0]), ["S", "T", "k"]);
    assert!(
        matches!(
            where_decls(&decls[0])[1].body,
            SurfaceExpr::Universe(_, UniverseExpr::SortImplicit)
        ),
        "{:?}",
        where_decls(&decls[0])[1].body
    );
}

#[test]
fn where_decls_after_match_alternatives_and_on_a_theorem() {
    let decls = parse_without_recovery(
        "def f : Nat → Nat\n  | 0 => k\n  | n+1 => f n\nwhere\n  T := Type\n  k := 3\n\n\
         theorem t : True := h\nwhere\n  T := Type\n  h : True := trivial\n",
    );
    assert_eq!(where_names(&decls[0]), ["T", "k"]);
    assert_eq!(where_names(&decls[1]), ["T", "h"]);
}

/// Control: a level indented past the declaration column is still the level
/// (Lean reads `Sort u` here).
#[test]
fn level_indented_past_the_where_decl_column_is_still_the_level() {
    let decls = parse_without_recovery(
        "universe u\ndef g : Nat := k\nwhere\n  T := Sort\n    u\n  k := 3\n",
    );
    let def = decls
        .iter()
        .find(|d| matches!(d, SurfaceDecl::Def { .. }))
        .expect("the def");
    assert_eq!(where_names(def), ["T", "k"]);
    let body = &where_decls(def)[0].body;
    assert!(
        sort_level(body).is_some_and(|l| is_param(l, "u")),
        "{body:?}"
    );
}

// ─── A Lean keyword is never a level ────────────────────────────────────────
//
// `Level.ident := checkPrec maxPrec >> Parser.ident` (`Lean/Parser/Level.lean`)
// and Lean's `ident` never matches a token-table keyword, so `optional
// levelParser` reads no level before `at`, `local`, `initialize`, …. Each
// source below is accepted by Lean 4.30.0-rc2.

/// Parse a whole file and require no recovery at all: no raw declaration and
/// no recovery diagnostic (a tactic-block error recovers with a diagnostic
/// only).
fn parse_cleanly(src: &str) -> Vec<SurfaceDecl> {
    let report = crate::parse_file_with_diagnostics(src)
        .unwrap_or_else(|e| panic!("must parse, got {e:?}\n{src}"));
    assert!(
        report.diagnostics.is_empty(),
        "no recovery diagnostic is allowed; got {:?}\n{src}",
        report.diagnostics
    );
    assert!(
        !report
            .decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "no declaration may fall to parser recovery; got {:?}\n{src}",
        report.decls
    );
    report.decls
}

fn def_value<'a>(decls: &'a [SurfaceDecl], name: &str) -> &'a SurfaceExpr {
    decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Def { name: n, val, .. } if n.to_string() == name => Some(val.as_ref()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("def {name} must be parsed: {decls:?}"))
}

/// `change … at h` separates the location from a bare universe sort or an
/// explicit level, keeping the tactic block free of parser recovery.
#[test]
fn tactic_keyword_after_type_is_not_a_level() {
    parse_cleanly(
        "example (T : Type 1) (h : T = Type) : True := by\n  change T = Type at h\n  trivial\n",
    );
    parse_cleanly(
        "example (T : Type 1) (h : T = Sort 1) : True := by\n  change T = Sort 1 at h\n  \
         change T = Type at h\n  trivial\n",
    );
}

#[test]
fn command_keyword_after_type_is_not_a_level() {
    let decls = parse_cleanly(
        "def Carrier : Type 1 := Type\nlocal notation \"CC\" => Carrier\n\
         def useC : Type 1 := CC\n",
    );
    assert!(is_bare_type(def_value(&decls, "Carrier")), "{decls:?}");
    def_value(&decls, "useC");
}

/// `initialize` is a keyword as well, so `def T` keeps a `Type` with no
/// level (before, `Type initialize` refused the name and `def T` was lost).
/// The `initialize` line itself still falls to recovery, for a reason the
/// level guard does not own: the application loop takes the line-start
/// keyword as an ARGUMENT, and `def T : Nat := 1` ⏎ `initialize …` reads
/// `1 initialize counter` the same way. Only the level is asserted here.
#[test]
fn initialize_after_type_is_not_a_level() {
    let decls = Parser::parse_file(
        "def T : Type 1 := Type\ninitialize counter : IO.Ref Nat ← IO.mkRef 0\n",
    )
    .expect("should parse");
    let value = def_value(&decls, "T");
    let head = match value {
        SurfaceExpr::App(_, head, _) => head.as_ref(),
        other => other,
    };
    assert!(is_bare_type(head), "`Type` reads no level: {value:?}");
}

/// Control: an escaped `«at»` is an identifier, so it IS a level.
#[test]
fn escaped_keyword_spelling_is_a_level() {
    let expr = Parser::parse_expr("Type «at»").expect("should parse");
    assert!(
        type_level(&expr).is_some_and(|l| is_param(l, "at")),
        "{expr:?}"
    );
}

// ─── Bracketed binders parse `withoutPosition` ──────────────────────────────
//
// `explicitBinder`, `implicitBinder` and `instBinder`
// (`Lean/Parser/Term/Basic.lean:205-248`) parse their contents
// `withoutPosition`, so inside the brackets a level on a continuation line
// at or left of an enclosing block's saved column is still the level. Each
// source below is accepted by Lean 4.30.0-rc2. `strictImplicitBinder` has no
// `withoutPosition`; see the strict-implicit controls further down.

fn first_binder_type(e: &SurfaceExpr) -> &SurfaceExpr {
    match e {
        SurfaceExpr::Pi(_, binders, _) | SurfaceExpr::Lambda(_, binders, _) => binders[0]
            .ty
            .as_deref()
            .unwrap_or_else(|| panic!("the first binder is typed: {e:?}")),
        other => panic!("expected a binder telescope, got {other:?}"),
    }
}

fn binder_sort_is_u(field_ty: &SurfaceExpr) -> bool {
    sort_level(first_binder_type(field_ty)).is_some_and(|l| is_param(l, "u"))
}

#[test]
fn implicit_binder_arrow_level_continuation_in_a_field() {
    let decls = parse_cleanly(
        "universe u\nstructure S where\n    f : {α : Sort\n  u} → α → α\n    n : Nat\n",
    );
    let fields = structure_fields(&decls[1]);
    assert_eq!(names(fields), ["f", "n"]);
    assert!(binder_sort_is_u(&fields[0].ty), "{:?}", fields[0].ty);
}

#[test]
fn explicit_binder_arrow_level_continuation_in_a_field() {
    let decls = parse_cleanly(
        "universe u\nstructure S where\n    f : (α : Sort\n  u) → α → α\n    n : Nat\n",
    );
    let fields = structure_fields(&decls[1]);
    assert_eq!(names(fields), ["f", "n"]);
    assert!(binder_sort_is_u(&fields[0].ty), "{:?}", fields[0].ty);
}

#[test]
fn forall_binder_level_continuations_in_a_field() {
    for src in [
        "universe u\nstructure S where\n    f : ∀ {α : Sort\n  u}, α → α\n    n : Nat\n",
        "universe u\nstructure S where\n    f : ∀ (α : Sort\n  u), α → α\n    n : Nat\n",
    ] {
        let decls = parse_cleanly(src);
        let fields = structure_fields(&decls[1]);
        assert_eq!(names(fields), ["f", "n"], "{src}");
        assert!(binder_sort_is_u(&fields[0].ty), "{:?}\n{src}", fields[0].ty);
    }
    // The second of two groups, after a same-line first group.
    let decls = parse_cleanly(
        "universe u\nstructure S where\n    f : ∀ {α : Sort u} {β : Sort\n  u}, α → β → α\n    \
         n : Nat\n",
    );
    assert_eq!(names(structure_fields(&decls[1])), ["f", "n"]);
}

#[test]
fn instance_binder_argument_continuation_in_a_field() {
    let decls = parse_cleanly(
        "universe u\nclass K (α : Sort u) where\n  x : Nat\nstructure S where\n    \
         f : ∀ (α : Type) [inst : K\n  α], Nat\n    n : Nat\n",
    );
    let fields = structure_fields(&decls[2]);
    assert_eq!(names(fields), ["f", "n"]);
    match &fields[0].ty {
        SurfaceExpr::Pi(_, binders, _) => {
            let inst_ty = binders[1].ty.as_deref().expect("typed instance binder");
            assert!(
                matches!(inst_ty, SurfaceExpr::App(_, _, args) if args.len() == 1),
                "`K α` keeps its argument: {inst_ty:?}"
            );
        }
        other => panic!("expected a Pi, got {other:?}"),
    }
}

#[test]
fn fun_binder_level_continuation_in_an_instance_field() {
    let decls = parse_cleanly(
        "universe u\nclass C where\n    g : ∀ (α : Sort u), α → α\ninstance : C where\n    \
         g := fun (α : Sort\n  u) (x : α) => x\n",
    );
    match &decls[2] {
        SurfaceDecl::Instance { fields, .. } => {
            assert_eq!(assign_names(fields), ["g"]);
            assert!(binder_sort_is_u(&fields[0].val), "{:?}", fields[0].val);
        }
        other => panic!("expected an instance, got {other:?}"),
    }
}

#[test]
fn binder_level_continuation_in_a_tactic_have() {
    parse_cleanly(
        "universe u\nexample : True := by\n  have _h : ∀ {α : Sort\n  u}, α → α := fun x => x\n  \
         trivial\n",
    );
}

#[test]
fn binder_level_continuation_in_a_where_decl_header() {
    let decls = parse_cleanly(
        "universe u\ndef g : Nat := k\nwhere\n  h (α : Sort\n  u) (x : α) : α := x\n  k := 3\n",
    );
    let def = decls
        .iter()
        .find(|d| matches!(d, SurfaceDecl::Def { .. }))
        .expect("the def");
    assert_eq!(where_names(def), ["h", "k"]);
    let alpha = where_decls(def)[0].binders[0]
        .ty
        .as_deref()
        .expect("typed binder");
    assert!(
        sort_level(alpha).is_some_and(|l| is_param(l, "u")),
        "{alpha:?}"
    );
}

/// `strictImplicitBinder` (`⦃…⦄` and `{{…}}`) parses its contents WITH the
/// enclosing position (`Lean/Parser/Term/Basic.lean:233-235`), so Lean
/// 4.30.0-rc2 refuses a level continuation at or left of the field column:
/// "unexpected identifier; expected '}' or '⦄'". Clean refuses it too.
#[test]
fn strict_implicit_binder_keeps_the_saved_position() {
    for src in [
        "universe u\nstructure S where\n    f : ∀ ⦃α : Sort\n  u⦄, α → α\n    n : Nat\n",
        "universe u\nstructure S where\n    f : ∀ {{α : Sort\n  u}}, α → α\n    n : Nat\n",
    ] {
        let clean = crate::parse_file_with_diagnostics(src).is_ok_and(|report| {
            report.diagnostics.is_empty()
                && !report
                    .decls
                    .iter()
                    .any(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        });
        assert!(
            !clean,
            "Lean refuses this; Clean must not accept it:\n{src}"
        );
    }
    // Control: on one line both spellings parse.
    let decls = parse_cleanly(
        "universe u\nstructure S where\n    f : ∀ ⦃α : Sort u⦄, α → α\n    \
         g : ∀ {{α : Sort u}}, α → α\n    n : Nat\n",
    );
    assert_eq!(names(structure_fields(&decls[1])), ["f", "g", "n"]);
}
