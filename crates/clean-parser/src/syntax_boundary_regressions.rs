// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{parse_expr, parse_file, SurfaceDecl, SurfaceExpr};

#[test]
fn test_parse_syntax_decl_boundary_before_hash_check_command() {
    let code = r#"
syntax "👉" (ident <|> "_") : term
#check Nat.succ
"#;
    let decls =
        parse_file(code).expect("syntax declaration followed by #check should parse cleanly");
    assert_eq!(
        decls.len(),
        2,
        "expected syntax + #check declarations, got {decls:?}"
    );
    assert!(
        matches!(decls.first(), Some(SurfaceDecl::Syntax { .. })),
        "first declaration should be syntax, got {:?}",
        decls.first()
    );
    assert!(
        matches!(decls.get(1), Some(SurfaceDecl::Check { .. })),
        "second declaration should be #check, got {:?}",
        decls.get(1)
    );
}

#[test]
fn test_parse_syntax_decl_boundary_before_hash_print_command() {
    let code = r#"
syntax (name := fooParser) "foo" term : term
#print Nat.rec
"#;
    let decls =
        parse_file(code).expect("syntax declaration followed by #print should parse cleanly");
    assert_eq!(
        decls.len(),
        2,
        "expected syntax + #print declarations, got {decls:?}"
    );
    assert!(
        matches!(decls.first(), Some(SurfaceDecl::Syntax { .. })),
        "first declaration should be syntax, got {:?}",
        decls.first()
    );
    assert!(
        matches!(decls.get(1), Some(SurfaceDecl::Print { .. })),
        "second declaration should be #print, got {:?}",
        decls.get(1)
    );
}

#[test]
fn test_parse_syntax_decl_boundary_before_private_modifier() {
    let code = r#"
syntax "kdef " ident " := " term : command
private def hidden : Nat := 0
"#;
    let decls =
        parse_file(code).expect("syntax declaration followed by private def should parse cleanly");
    assert_eq!(
        decls.len(),
        2,
        "expected syntax + private def declarations, got {decls:?}"
    );
    assert!(
        matches!(decls.first(), Some(SurfaceDecl::Syntax { .. })),
        "first declaration should be syntax, got {:?}",
        decls.first()
    );
    assert!(
        matches!(decls.get(1), Some(SurfaceDecl::Def { .. })),
        "second declaration should be def, got {:?}",
        decls.get(1)
    );
}

/// Regression test for #2832: `.{ field := value }` anonymous constructor syntax.
/// The parser previously rejected LBrace after a leading dot, producing
/// "expected identifier after '.', got LBrace".
fn expect_dot_brace_struct_lit(expr: SurfaceExpr, expected_fields: &[&str]) -> Result<(), String> {
    match expr {
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            if struct_type.is_some() {
                return Err(format!("unexpected type annotation: {struct_type:?}"));
            }
            if base.is_some() {
                return Err(format!("unexpected base expression: {base:?}"));
            }
            if fields.len() != expected_fields.len() {
                return Err(format!(
                    "expected {} fields, got {}: {fields:?}",
                    expected_fields.len(),
                    fields.len()
                ));
            }
            for (field, expected_name) in fields.iter().zip(expected_fields.iter()) {
                if field.name != *expected_name {
                    return Err(format!(
                        "expected field `{expected_name}`, got `{}`",
                        field.name
                    ));
                }
            }
            Ok(())
        }
        other => Err(format!("expected StructLit, got {other:?}")),
    }
}

#[test]
fn test_dot_brace_anonymous_constructor_single_field() -> Result<(), String> {
    let expr = parse_expr(".{ x := 1 }")
        .map_err(|err| format!("Failed to parse .{{ x := 1 }}: {err:?}"))?;
    expect_dot_brace_struct_lit(expr, &["x"])
}

#[test]
fn test_dot_brace_anonymous_constructor_multiple_fields() -> Result<(), String> {
    let expr = parse_expr(".{ x := 1, y := 2 }")
        .map_err(|err| format!("Failed to parse .{{ x := 1, y := 2 }}: {err:?}"))?;
    expect_dot_brace_struct_lit(expr, &["x", "y"])
}

#[test]
fn test_dot_brace_anonymous_constructor_empty() -> Result<(), String> {
    let expr = parse_expr(".{}").map_err(|err| format!("Failed to parse .{{}}: {err:?}"))?;
    expect_dot_brace_struct_lit(expr, &[])
}

/// Regression tests for #2835: VeriSoftBench parser compatibility.
/// Tests various `if` patterns that appear in real Lean 4 code from the Binius
/// BinaryBasefold formalization.

#[test]
fn test_verisoftbench_decidable_if_simple() {
    let code = "def f := if hj : x < y then a else b";
    parse_file(code).expect("decidable if should parse");
}

#[test]
fn test_verisoftbench_nested_if_with_named_args() {
    let code = "def f := if hj : x < y then if g (k := j) (n := idx) = 0 then 0 else 1 else c";
    parse_file(code).expect("nested if with named args should parse");
}

#[test]
fn test_verisoftbench_if_with_anon_ctor_else() {
    let code = r#"def f := if hj : x < y then a else g ⟨x, by admit⟩"#;
    parse_file(code).expect("if with anonymous constructor in else branch should parse");
}

#[test]
fn test_verisoftbench_if_then_by_else_by() {
    let code = "def f := if h : x = 0 then by exact a else by exact b";
    parse_file(code).expect("if then by ... else by ... should parse");
}

#[test]
fn test_verisoftbench_fiber_coeff_pattern() {
    // Simplified version of the fiber_coeff definition from Binius
    let code = r#"def fiber_coeff (hj : Prop) (elem : Nat) (y : Nat) : Nat :=
  if hj : x < y then
    if f (k := j) (n := elem) = 0 then 0 else 1
  else y"#;
    parse_file(code).expect("fiber_coeff-like definition should parse");
}

#[test]
fn test_verisoftbench_if_then_by_multiline() {
    // Multi-line if-then-by pattern from qMap_total_fiber
    let code = r#"def f :=
  if h : x = 0 then by
    exact a
  else by
    exact b"#;
    parse_file(code).expect("multi-line if then by ... else by should parse");
}

#[test]
fn test_verisoftbench_set_builder_with_exists() {
    // Set builder notation: {y | ∃ x, ...}
    let code = r#"def s := {y | x = y}"#;
    parse_file(code).expect("set builder notation should parse");
}

#[test]
fn test_verisoftbench_named_arg_in_struct() {
    // Named argument := syntax inside struct field
    let code = r#"def f := g (h_rate := h) ⟨i, by admit⟩"#;
    parse_file(code).expect("named arg followed by anon ctor should parse");
}

/// Regression test for #2835: same-line `by` block must terminate at `else`.
/// The `by` block's tactic parser was not recognizing `else` as a terminator
/// when the indent stack was non-empty (same-line case), causing it to
/// consume past `else` and fail with "expected Else, got Comma/Eof".
#[test]
fn test_by_block_terminates_at_else_same_line() {
    // Decidable if with by blocks on both branches (same line)
    let code = "def f := if h : x = 0 then by exact a else by exact b";
    parse_file(code).expect("same-line by blocks in if-then-else should parse");

    // Regular if with by blocks
    let code2 = "def f := if x then by exact a else by exact b";
    parse_file(code2).expect("regular if with same-line by blocks should parse");
}

/// Ensure that tactic-level `if-then-else` inside `by` blocks still works
/// (the `else` is consumed by `if_body`, not `at_tactic_end`).
#[test]
fn test_by_block_tactic_if_still_works() {
    let code = r#"def f := by
  if h : x = 0 then exact a else exact b"#;
    parse_file(code).expect("tactic-level if-then-else inside by block should parse");
}

/// A LEADING-DOT pattern is a constructor reference, never a binder.
///
/// The `Dot` arm consumed the dot and re-entered the pattern parser, whose
/// `Ident` arm cannot see that a dot preceded it — so the nullary case came back
/// as `Var(name)`, a BINDER. A misspelled constructor therefore became a silent
/// catch-all:
///
/// ```text
/// match c with
/// | .reddd => 1      -- typo, parsed as a binder that matches everything
/// | .green => 2      -- dead arm
/// ```
///
/// `g Col.green` reduced to `1`, and the match still looked exhaustive — a typo
/// changed the program's meaning with no diagnostic. This asserts the re-tag on
/// the AST, so it fails if the `Dot` arm ever drops it again.
#[test]
fn test_leading_dot_nullary_pattern_is_ctor_not_binder() {
    let code = r#"def g (c : Col) : Nat :=
  match c with
  | .reddd => 1
  | .green => 2"#;
    let parsed = parse_file(code).expect("dotted nullary patterns should parse");
    let dumped = format!("{parsed:?}");

    assert!(
        !dumped.contains(r#"Var("reddd")"#),
        "a leading-dot pattern must never become a binder — `.reddd` as \
         `Var(\"reddd\")` silently swallows every constructor; got: {dumped}"
    );
    assert!(
        dumped.contains(r#"Ctor("reddd", [])"#),
        "`.reddd` must be a nullary Ctor so the name resolves like any other \
         dotted constructor (and an unknown one fails loudly); got: {dumped}"
    );
}

/// The re-tag is confined to the leading-dot case.
///
/// An APPLIED dotted pattern already parsed as `Ctor`, and a bare identifier in
/// pattern position is a genuine binder that must stay a `Var` — re-tagging it
/// would turn every pattern variable into an unknown constructor.
#[test]
fn test_leading_dot_retag_leaves_applied_ctors_and_real_binders_alone() {
    let applied = parse_file(
        r#"def f (l : L) : Nat :=
  match l with
  | .cons h t => 1
  | .nil => 0"#,
    )
    .expect("applied dotted patterns should parse");
    let applied = format!("{applied:?}");
    assert!(
        applied.contains(r#"Ctor("cons""#),
        "an applied dotted pattern stays a Ctor with its arguments; got: {applied}"
    );
    assert!(
        applied.contains(r#"Var("h")"#) && applied.contains(r#"Var("t")"#),
        "constructor ARGUMENTS are still binders — the re-tag must not reach \
         them; got: {applied}"
    );

    let binder = parse_file(
        r#"def f (n : Nat) : Nat :=
  match n with
  | x => x"#,
    )
    .expect("binder patterns should parse");
    let binder = format!("{binder:?}");
    assert!(
        binder.contains(r#"Var("x")"#),
        "a bare identifier with no leading dot is a real binder and must stay a \
         Var; got: {binder}"
    );
}

/// `Type` in ARGUMENT position is atomic — it must not swallow the next
/// argument as its universe level.
///
/// Lean parses an application argument at max precedence, where `Type` is
/// atomic; `Type u` there must be written `(Type u)`. Clean's `atom_expr` read
/// the level unconditionally, so
///
/// ```text
/// @Eq.rec Type Y (fun Z' h2' => …) rfl Z h2
/// ```
///
/// parsed as `@Eq.rec (Type Y) …` — one argument short, with the TERM variable
/// `Y` reinterpreted as a universe parameter. The elaborated type then carried
/// `Sort(Succ(Param(Y)))` and the declaration died with `CannotInfer`, taking
/// 16 more of `MType.lean`'s 49 declarations down with it.
#[test]
fn test_bare_type_in_argument_position_does_not_eat_the_next_argument() {
    let parsed = parse_file("def f := g Type y z").expect("should parse");
    let dumped = format!("{parsed:?}");
    assert!(
        !dumped.contains("TypeLevel"),
        "`Type` as an argument must stay the bare sort, not take `y` as a \
         universe level; got: {dumped}"
    );
    assert!(
        dumped.contains(r#"Ident(Span { start: 15, end: 16 }, "y")"#)
            || dumped.matches("Ident").count() >= 3,
        "`y` and `z` must survive as their own arguments; got: {dumped}"
    );
}

/// The suppression is scoped to the immediate argument atom.
///
/// A PARENTHESISED `(Type u)` argument still reads its level, and `Type u` in
/// an ordinary (non-argument) position is untouched — otherwise the fix above
/// would break every universe-polymorphic signature.
#[test]
fn test_parenthesised_and_non_argument_type_levels_still_parse() {
    let paren = format!(
        "{:?}",
        parse_file("def f := g (Type u) y").expect("should parse")
    );
    assert!(
        paren.contains("TypeLevel"),
        "a parenthesised `(Type u)` argument must still read its level; got: {paren}"
    );

    let ascription = format!(
        "{:?}",
        parse_file("def f (a : Type u) : Type u := a").expect("should parse")
    );
    assert!(
        ascription.contains("TypeLevel"),
        "`Type u` outside argument position must still read its level; got: {ascription}"
    );
}
