// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser grammar completions — gap-sweep brick B16.
//!
//! Parse-tree pins for the productions added in B16, plus the error-recovery
//! resynchronization guard. Each production's ground truth is Lean 4
//! (`src/Lean/Parser/{Term,Command,Basic}.lean`, `Init/Tactics.lean`); the pins
//! assert the Lean-shaped `SurfaceExpr`/`SurfaceDecl` each construct produces.
//!
//! Covered rows (docs/plans/GAP_SWEEP_2026-07-09.md §B16):
//!   term_sugar/p03  `suffices h : P from e` (newline continuation)
//!   term_sugar/p16  `‹P›` anonymous hypothesis
//!   term_sugar/p20  `‹P›` (loud reject is at elaboration, parse is well-formed)
//!   structures/p10  `make ::` structCtor
//!   structures/p14  `{ o with inner.v := 3 }` nested structInstLVal
//!   classes_instances/p19  `class inductive`
//!   universes/p06,p36  `.{u, v}` multi-param universe binder
//!   literals/p03,p07,p08   `\uXXXX` char/string escapes
//!   + error-recovery resync (one bad decl does not swallow the following decl)

use clean_parser::{
    parse_decl, parse_expr, parse_file, Projection, SurfaceDecl, SurfaceExpr, SurfaceLit,
    SurfaceTactic,
};

// ---------------------------------------------------------------------------
// term_sugar/p03 — `suffices h : P from e` with a newline-separated body
// ---------------------------------------------------------------------------

/// `suffices h : a = b from Eq.symm h` followed by the continuation proof `hab`
/// on the next line (no `;`, both at the same layout column) parses — Lean's
/// `optSemicolon` makes the separator optional and the newline-dedent ends the
/// justification. Desugars to `let h : (a = b) := hab; Eq.symm h`.
const SUFFICES_PROBE: &str =
    "theorem sfA (a b : Nat) (hab : a = b) : b = a :=\n  suffices h : a = b from Eq.symm h\n  hab";

fn suffices_probe_proof() -> SurfaceExpr {
    match parse_decl(SUFFICES_PROBE).expect("suffices/from newline theorem parses") {
        SurfaceDecl::Theorem { proof, .. } => *proof,
        other => panic!("expected Theorem, got {other:?}"),
    }
}

#[test]
fn test_suffices_from_newline_continuation_parses() {
    match suffices_probe_proof() {
        SurfaceExpr::Let(_, binder, value, justification) => {
            assert_eq!(binder.name, "h", "binder name");
            assert!(binder.ty.is_some(), "type `a = b` preserved");
            assert!(
                matches!(&*value, SurfaceExpr::Ident(_, n) if n == "hab"),
                "continuation `hab` becomes the let value, got {value:?}"
            );
            assert!(
                matches!(&*justification, SurfaceExpr::App(..)),
                "`Eq.symm h` justification is the let body, got {justification:?}"
            );
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

/// The compound type `a = b` (not a bare atom) must survive as the binder type.
#[test]
fn test_suffices_from_compound_type_is_full_expr() {
    let SurfaceExpr::Let(_, binder, _, _) = suffices_probe_proof() else {
        panic!("expected Let");
    };
    let ty = binder.ty.expect("type present");
    // `a = b` desugars to an `Eq` application — a full operator expr, not just `a`.
    assert!(
        matches!(&*ty, SurfaceExpr::App(..)),
        "type must be the full `a = b`, got {ty:?}"
    );
}

// ---------------------------------------------------------------------------
// term_sugar/p16,p20 — `‹P›` anonymous hypothesis
// ---------------------------------------------------------------------------

/// `‹n = 3›` parses to `(show (n = 3) by assumption)`, i.e. an ascription whose
/// term is a `by`-block running the `assumption` tactic (Lean `Init/Tactics.lean`
/// `‹$type›` macro).
#[test]
fn test_french_quote_desugars_to_by_assumption_ascription() {
    let expr = parse_expr("‹n = 3›").expect("french-quote hypothesis parses");
    match expr {
        SurfaceExpr::Ascription(_, term, ty) => {
            match &*term {
                SurfaceExpr::ByTactic(_, tacs) => {
                    assert_eq!(tacs.len(), 1, "one tactic");
                    assert!(
                        matches!(&tacs[0], SurfaceTactic::Named { name, .. } if name == "assumption"),
                        "the tactic is `assumption`, got {:?}",
                        tacs[0]
                    );
                }
                other => panic!("expected ByTactic term, got {other:?}"),
            }
            assert!(
                matches!(&*ty, SurfaceExpr::App(..)),
                "ascribed type is `n = 3`, got {ty:?}"
            );
        }
        other => panic!("expected Ascription, got {other:?}"),
    }
}

/// `‹P›` in argument position is a well-formed atom (used inside a larger term).
#[test]
fn test_french_quote_is_atom_in_application() {
    let expr = parse_expr("f ‹p›").expect("french-quote as argument parses");
    assert!(
        matches!(expr, SurfaceExpr::App(..)),
        "‹p› as an argument yields an application, got {expr:?}"
    );
}

// ---------------------------------------------------------------------------
// structures/p10 — `make ::` custom constructor name
// ---------------------------------------------------------------------------

/// `structure Point where make :: x : Nat y : Nat` captures the custom
/// constructor name `make` (Lean `structCtor`), keeping the two fields.
#[test]
fn test_struct_custom_ctor_name_captured() {
    let decl = parse_decl("structure Point where\n  make ::\n  x : Nat\n  y : Nat")
        .expect("structCtor parses");
    match decl {
        SurfaceDecl::Structure {
            name,
            ctor_name,
            fields,
            ..
        } => {
            assert_eq!(name, "Point");
            assert_eq!(ctor_name.as_deref(), Some("make"), "custom ctor name");
            assert_eq!(fields.len(), 2, "both fields parsed");
            assert_eq!(fields[0].name, "x");
            assert_eq!(fields[1].name, "y");
        }
        other => panic!("expected Structure, got {other:?}"),
    }
}

/// Without `make ::`, `ctor_name` is `None` (default `mk`) — no behavior change.
#[test]
fn test_struct_default_ctor_name_is_none() {
    let decl = parse_decl("structure Point where\n  x : Nat\n  y : Nat").expect("parses");
    let SurfaceDecl::Structure { ctor_name, .. } = decl else {
        panic!("expected Structure");
    };
    assert_eq!(ctor_name, None, "default ctor keeps None");
}

// ---------------------------------------------------------------------------
// structures/p14 — `{ o with inner.v := 3 }` nested structInstLVal
// ---------------------------------------------------------------------------

/// A dotted field path in a struct update desugars, at parse time, to a nested
/// update on the projected subobject: `{ o with inner.v := 3 }` ⇒
/// `{ o with inner := { o.inner with v := 3 } }` (Lean's `StructInst` grouping).
#[test]
fn test_nested_struct_inst_lval_desugars() {
    let expr = parse_expr("{ o with inner.v := 3 }").expect("nested lval parses");
    let SurfaceExpr::StructLit { base, fields, .. } = expr else {
        panic!("expected StructLit");
    };
    // Outer base is `o`.
    assert!(
        matches!(base.as_deref(), Some(SurfaceExpr::Ident(_, n)) if n == "o"),
        "outer base is `o`, got {base:?}"
    );
    assert_eq!(fields.len(), 1, "single top-level field `inner`");
    assert_eq!(fields[0].name, "inner");
    // Its value is the nested update `{ o.inner with v := 3 }`.
    match &fields[0].val {
        SurfaceExpr::StructLit {
            base: inner_base,
            fields: inner_fields,
            ..
        } => {
            assert!(
                matches!(
                    inner_base.as_deref(),
                    Some(SurfaceExpr::Proj(_, obj, Projection::Named(f)))
                        if matches!(&**obj, SurfaceExpr::Ident(_, n) if n == "o") && f == "inner"
                ),
                "inner base is the projection `o.inner`, got {inner_base:?}"
            );
            assert_eq!(inner_fields.len(), 1);
            assert_eq!(inner_fields[0].name, "v");
            assert!(
                matches!(
                    &inner_fields[0].val,
                    SurfaceExpr::Lit(_, SurfaceLit::Nat(3))
                ),
                "inner value is `3`, got {:?}",
                inner_fields[0].val
            );
        }
        other => panic!("expected nested StructLit for `inner`, got {other:?}"),
    }
}

/// A plain (non-dotted) struct update is unchanged by the nested-path support.
#[test]
fn test_plain_struct_update_unchanged() {
    let expr = parse_expr("{ p with y := 3 }").expect("plain update parses");
    let SurfaceExpr::StructLit { fields, base, .. } = expr else {
        panic!("expected StructLit");
    };
    assert!(base.is_some(), "has a `with` base");
    assert_eq!(fields.len(), 1);
    assert_eq!(fields[0].name, "y");
    assert!(
        matches!(&fields[0].val, SurfaceExpr::Lit(_, SurfaceLit::Nat(3))),
        "y := 3 stays a direct assignment, got {:?}",
        fields[0].val
    );
}

// ---------------------------------------------------------------------------
// classes_instances/p19 — `class inductive`
// ---------------------------------------------------------------------------

/// `class inductive Foo … where | a | b` parses as an inductive with its
/// constructors (the class-registration is descoped; the type + ctors register
/// exactly as a plain inductive, which is what Lean accepts for the decl).
#[test]
fn test_class_inductive_parses_as_inductive() {
    let decl = parse_decl(
        "class inductive MyDec (p : Prop) : Type where\n  | isFalse (h : p) : MyDec p\n  | isTrue (h : p) : MyDec p",
    )
    .expect("class inductive parses");
    match decl {
        SurfaceDecl::Inductive { name, ctors, .. } => {
            assert_eq!(name, "MyDec");
            assert_eq!(ctors.len(), 2, "both constructors parsed");
            assert_eq!(ctors[0].name, "isFalse");
            assert_eq!(ctors[1].name, "isTrue");
        }
        other => panic!("expected Inductive, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// universes/p06,p36 — `.{u, v}` multi-param universe binder
// ---------------------------------------------------------------------------

/// `def two.{u, v} …` records both comma-separated universe params (Lean
/// `declId` universe binders). The single-param `.{u}` form already worked.
#[test]
fn test_multi_param_universe_binder() {
    let decl = parse_decl("def two.{u, v} (a : Nat) : Nat := a").expect("`.{u, v}` parses");
    let SurfaceDecl::Def {
        universe_params, ..
    } = decl
    else {
        panic!("expected Def");
    };
    assert_eq!(universe_params, vec!["u".to_string(), "v".to_string()]);
}

/// Space-separated `.{u v}` (no comma) is still accepted.
#[test]
fn test_multi_param_universe_binder_space_separated() {
    let decl = parse_decl("def two.{u v} (a : Nat) : Nat := a").expect("`.{u v}` parses");
    let SurfaceDecl::Def {
        universe_params, ..
    } = decl
    else {
        panic!("expected Def");
    };
    assert_eq!(universe_params, vec!["u".to_string(), "v".to_string()]);
}

// ---------------------------------------------------------------------------
// literals/p03,p07,p08 — `\uXXXX` char/string escapes
// ---------------------------------------------------------------------------

/// `"Aα"` — braceless four-hex-digit unicode escapes in a string
/// (Lean `quotedCharFn`): resolves to `Aα`.
#[test]
fn test_string_braceless_unicode_escape() {
    let expr = parse_expr("\"\\u0041\\u03B1\"").expect("string \\uXXXX parses");
    match expr {
        SurfaceExpr::Lit(_, SurfaceLit::String(s)) => assert_eq!(s, "Aα"),
        other => panic!("expected string literal, got {other:?}"),
    }
}

/// `'α'` — braceless four-hex-digit unicode escape in a char literal → `α`.
#[test]
fn test_char_braceless_unicode_escape() {
    let expr = parse_expr("'\\u03B1'").expect("char \\uXXXX parses");
    match expr {
        SurfaceExpr::Lit(_, SurfaceLit::Char(c)) => assert_eq!(c, 'α'),
        other => panic!("expected char literal, got {other:?}"),
    }
}

/// The braced `\u{...}` form remains accepted (retained superset).
#[test]
fn test_char_braced_unicode_escape_still_works() {
    let expr = parse_expr("'\\u{3B1}'").expect("char \\u{..} still parses");
    assert!(matches!(expr, SurfaceExpr::Lit(_, SurfaceLit::Char('α'))));
}

// ---------------------------------------------------------------------------
// error-recovery resync — one bad decl must not swallow the next
// ---------------------------------------------------------------------------

/// A malformed first declaration (an unterminated char literal) must recover to
/// a `RawDecl` WITHOUT swallowing the following declarations: the char lexer no
/// longer scans across a newline, so `def good`/`theorem good_pin` still parse
/// as their own decls (gap sweep: the literals/p08 recovery cascade).
#[test]
fn test_recovery_resync_does_not_swallow_following_decls() {
    let decls = parse_file(
        "def bad : Char := 'xy\ndef good : Nat := 5\ntheorem good_pin : good = 5 := rfl",
    )
    .expect("file parses with recovery");
    // First decl recovered as a RawDecl (the malformed char).
    assert!(
        matches!(decls.first(), Some(SurfaceDecl::RawDecl { .. })),
        "first decl is a recovery RawDecl, got {:?}",
        decls.first()
    );
    // The following good declarations survive intact.
    let names: Vec<&str> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } => Some(name.as_str()),
            SurfaceDecl::Theorem { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        names.contains(&"good"),
        "`def good` must survive recovery, got decls {names:?}"
    );
    assert!(
        names.contains(&"good_pin"),
        "`theorem good_pin` must survive recovery, got decls {names:?}"
    );
}

/// A single unterminated char immediately followed by a newline (`'a\n…`) must
/// also stop at the newline — the closing-quote scan must not consume the
/// newline and swallow the next declaration.
#[test]
fn test_recovery_resync_single_char_then_newline() {
    let decls = parse_file("def bad : Char := 'a\ndef good : Nat := 5").expect("parses");
    let names: Vec<&str> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        names.contains(&"good"),
        "`def good` must survive the `'a` unterminated char, got {names:?}"
    );
}

/// A dotted-path field with no `:=` (`{ Foo.bar }`) is NOT a struct field path —
/// it stays a collection/other literal, so the path detector cannot over-trigger.
#[test]
fn test_dotted_name_without_assign_is_not_a_field_path() {
    // Must not panic / mis-desugar; parses as some non-update expression.
    let expr = parse_expr("{ Nat.zero }").expect("collection-style brace parses");
    // Whatever it is, it must not be a `with`-update StructLit with a base.
    if let SurfaceExpr::StructLit { base, .. } = &expr {
        assert!(base.is_none(), "`{{ Nat.zero }}` has no update base");
    }
}
