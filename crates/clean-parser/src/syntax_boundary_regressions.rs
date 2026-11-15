// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{parse_expr, parse_file, SurfaceDecl, SurfaceExpr, SurfacePattern};

fn parsed_match_arms(decls: &[SurfaceDecl]) -> &[crate::SurfaceMatchArm] {
    match decls {
        [SurfaceDecl::Def { val, .. }] => match val.as_ref() {
            SurfaceExpr::Match(_, _, _, arms) => arms,
            other => panic!("expected a match body: {other:?}"),
        },
        other => panic!("expected one definition with a match body: {other:?}"),
    }
}

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
                if field.name.name() != crate::SurfaceName::component(*expected_name, false).name()
                {
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
    let arms = parsed_match_arms(&parsed);

    assert!(
        !matches!(&arms[0].pattern, SurfacePattern::Var(_)),
        "a leading-dot pattern must never become a binder — `.reddd` as \
         `Var(\"reddd\")` silently swallows every constructor; got: {parsed:?}"
    );
    assert!(
        matches!(&arms[0].pattern, SurfacePattern::Ctor(name, args)
            if name.name() == crate::SurfaceName::component("reddd", false).name()
                && name.is_relative_constructor() && args.is_empty()),
        "`.reddd` must be a nullary Ctor so the name resolves like any other \
         dotted constructor (and an unknown one fails loudly); got: {parsed:?}"
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
    let arms = parsed_match_arms(&applied);
    assert!(
        matches!(&arms[0].pattern, SurfacePattern::Ctor(name, args)
            if name.name() == crate::SurfaceName::component("cons", false).name()
                && name.is_relative_constructor() && args.len() == 2),
        "an applied dotted pattern stays a Ctor with its arguments; got: {applied:?}"
    );
    assert!(
        matches!(&arms[0].pattern, SurfacePattern::Ctor(_, args)
            if matches!(args.as_slice(), [SurfacePattern::Var(h), SurfacePattern::Var(t)]
                if h.same_syntax(&crate::SurfaceName::component("h", false))
                    && t.same_syntax(&crate::SurfaceName::component("t", false)))),
        "constructor ARGUMENTS are still binders — the re-tag must not reach \
         them; got: {applied:?}"
    );

    let binder = parse_file(
        r#"def f (n : Nat) : Nat :=
  match n with
  | x => x"#,
    )
    .expect("binder patterns should parse");
    let arms = parsed_match_arms(&binder);
    assert!(
        matches!(&arms[0].pattern, SurfacePattern::Var(name)
            if name.same_syntax(&crate::SurfaceName::component("x", false))),
        "a bare identifier with no leading dot is a real binder and must stay a \
         Var; got: {binder:?}"
    );
}

#[test]
fn relative_pattern_heads_keep_quoted_components_and_nested_selectors() {
    let parsed = parse_file("def f (x : T) := match x with\n  | .«c.d» => 0\n  | «.c.d» => 1\n  | .some .none => 2\n  | .rfl => 3\n").unwrap();
    let arms = parsed_match_arms(&parsed);
    assert!(matches!(&arms[0].pattern, SurfacePattern::Ctor(name, args)
        if name.same_syntax(&crate::SurfaceName::component("c.d", true).with_relative_constructor()) && args.is_empty()));
    assert!(matches!(&arms[1].pattern, SurfacePattern::Var(name)
        if name.same_syntax(&crate::SurfaceName::component(".c.d", true))));
    assert!(matches!(&arms[2].pattern, SurfacePattern::Ctor(outer, args)
        if outer.same_syntax(&crate::SurfaceName::component("some", false).with_relative_constructor())
            && matches!(args.as_slice(), [SurfacePattern::Ctor(inner, fields)]
                if inner.same_syntax(&crate::SurfaceName::component("none", false).with_relative_constructor()) && fields.is_empty())));
    // `.rfl` is Lean's `dotIdent` (`"." checkNoWsBefore rawIdent`): the
    // constructor `rfl` of the EXPECTED type's namespace, resolved like any
    // other `.c` — never the keyword pattern `rfl` (`Eq.refl`). Lean 4.8.0:
    // `match (h : 1 = 1) with | .rfl => 0` is "invalid dotted identifier
    // notation, unknown identifier `Eq.rfl` from expected type", and with
    // `inductive T | rfl | other`, `| .rfl =>` selects `T.rfl`.
    assert!(matches!(&arms[3].pattern, SurfacePattern::Ctor(name, args)
        if name.same_syntax(&crate::SurfaceName::component("rfl", false).with_relative_constructor())
            && args.is_empty()));
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

/// A SAME-LINE `ident :` at the top level of a structure-field type is the next
/// FIELD, not an application argument.
///
/// `structure Point where x : Nat y : Nat` parsed `Nat y` as an application:
/// the field-boundary break required the next field name to be
/// newline-preceded, so single-line multi-field structures died with
/// `TooManyArguments` plus a parser-recovery raw declaration. Sixteen of the
/// eighteen long-standing integration failures (coercion, matp, structure
/// regressions) were downstream of this one parse.
///
/// The boundary is gated on `field_delim_depth == 0`, so everything the
/// newline rule protected stays protected: a parenthesized `(f x : T)`
/// ascription or `(x y : T)` binder group inside a field type is inside a
/// delimiter, where the same-line arm never fires — the control test below
/// pins that direction.
#[test]
fn test_single_line_structure_fields_split_at_same_line_colon() {
    let parsed = parse_file("structure Point where x : Nat y : Nat")
        .expect("single-line multi-field structure should parse");
    let dumped = format!("{parsed:?}");
    assert!(
        dumped.contains(r#""x""#) && dumped.contains(r#""y""#),
        "both fields must survive; got: {dumped}"
    );
    assert!(
        !dumped.contains("recovery"),
        "no parser-recovery raw declaration; got: {dumped}"
    );

    // Three fields, projections downstream — the elaborator-visible shape.
    let three = format!(
        "{:?}",
        parse_file("structure P5 where x : Nat y : Nat z : Nat").expect("three fields")
    );
    for f in ["\"x\"", "\"y\"", "\"z\""] {
        assert!(three.contains(f), "field {f} must survive; got: {three}");
    }
}

/// The other direction: a same-line ascription INSIDE a delimiter within a
/// field type must NOT be split into a phantom field.
#[test]
fn test_field_type_ascription_inside_delimiters_stays_intact() {
    let parsed = parse_file("structure P4 where\n  f : Nat → Nat\n  h : (2 : Nat) = 2")
        .expect("ascription inside a field type should parse");
    let dumped = format!("{parsed:?}");
    assert!(
        dumped.contains(r#""f""#) && dumped.contains(r#""h""#),
        "exactly the two declared fields; got: {dumped}"
    );
}

/// Parenthesized field binder groups inside a `where` block — Lean's
/// `structFields` shape `structure P where (x : Nat) (y : Nat)`.
///
/// Before the LParen arm in the field loop, these groups fell OUT of the
/// `where` block entirely: the structure was SILENTLY accepted with ZERO
/// fields and the group tokens resurfaced as a junk `RawDecl` — the
/// audit's "wrong program silently accepted" failure shape, measured on
/// every spelling below.
#[test]
fn test_structure_where_paren_field_groups_parse_as_fields() {
    for (src, want_fields) in [
        ("structure P3 where (x : Nat) (y : Nat)", vec!["x", "y"]),
        // A multi-name group expands to one field per name.
        ("structure P4 where\n  (x y : Nat)", vec!["x", "y"]),
        // Groups interleave with simple fields.
        ("structure P5 where\n  (x : Nat)\n  y : Nat", vec!["x", "y"]),
        (
            "structure P7 where\n  a : Nat\n  (b c : Nat)",
            vec!["a", "b", "c"],
        ),
    ] {
        let decls = parse_file(src).expect("paren field groups must parse");
        assert_eq!(decls.len(), 1, "{src}: exactly one decl, got {decls:?}");
        let Some(SurfaceDecl::Structure { fields, .. }) = decls.first() else {
            panic!("{src}: expected a structure, got {decls:?}");
        };
        let names: Vec<crate::SurfaceName> = fields.iter().map(|f| f.name.clone()).collect();
        assert_eq!(
            names,
            want_fields
                .iter()
                .map(|name| crate::SurfaceName::component(name, false))
                .collect::<Vec<_>>(),
            "{src}: field names"
        );
    }
}

/// A paren group carries an optional GROUP default — `(x : Nat := 3)` — and
/// the default applies to every name in its group.
#[test]
fn test_structure_where_paren_field_group_default() {
    let decls = parse_file("structure P6 where (x y : Nat := 3)").expect("group default parses");
    let Some(SurfaceDecl::Structure { fields, .. }) = decls.first() else {
        panic!("expected a structure, got {decls:?}");
    };
    assert_eq!(fields.len(), 2, "one field per name in the group");
    for f in fields {
        assert!(
            f.default.is_some(),
            "the group default must apply to `{}`",
            f.name
        );
    }
}

/// The same gap existed for `class` `where` blocks.
#[test]
fn test_class_where_paren_field_groups_parse_as_fields() {
    let decls =
        parse_file("class C1 (a : Type) where (op : a)\n").expect("class paren group parses");
    assert_eq!(decls.len(), 1, "exactly one decl, got {decls:?}");
    let Some(SurfaceDecl::Class { fields, .. }) = decls.first() else {
        panic!("expected a class, got {decls:?}");
    };
    let names: Vec<crate::SurfaceName> = fields.iter().map(|f| f.name.clone()).collect();
    assert_eq!(
        names,
        vec![crate::SurfaceName::generated_path("op")],
        "class paren-group field names"
    );
}

/// `haveI` / `letI` are keywords that lex as identifiers, so the
/// `(ident := e)` named-argument lookahead used to claim `(haveI := A; body)`
/// and die on the `;` — Mathlib's `Preorder.ext {A B : Preorder α} (H : ∀ x y,
/// (haveI := A; x ≤ y) ↔ x ≤ y)` family, six raw-declaration rows in
/// `Mathlib/Order/Basic.lean` (measured 2026-09-11).
#[test]
fn test_parenthesized_anonymous_have_i_is_a_have_body_not_a_named_argument() {
    let code = "def a1 (A : Nat) : Nat := (haveI := A; A)\n\
                def a6 (A : Nat) (H : ∀ x : Nat, (haveI := A; x = x) ↔ x = x) : Nat := A\n";
    let decls = parse_file(code).expect("parenthesized `haveI := A; body` must parse");
    assert_eq!(decls.len(), 2, "two declarations, got {decls:?}");
    for d in &decls {
        assert!(
            !matches!(d, SurfaceDecl::RawDecl { .. }),
            "no declaration may fall into recovery, got {d:?}"
        );
    }
    // A genuine named argument is untouched.
    let named = parse_expr("f (α := Nat)").expect("named argument must still parse");
    assert!(
        matches!(named, SurfaceExpr::App(..)),
        "`f (α := Nat)` is an application with a named argument, got {named:?}"
    );
}

/// An anonymous instance binder `[Std.Refl r]` is the application of the
/// dotted class name to `r` — the same expression `(h : Std.Refl r)` and the
/// result type `: Std.Refl r` already produce. The anonymous path used to
/// rebuild the type from the identifier TOKENS it had collected, and lost
/// everything but the first component of a dotted head, so the elaborator saw
/// `Std` applied to `r` and auto-bound `Std` (`Std.Refl.compl`,
/// `Std.Irrefl.compl`, `rel_imp_eq_of_rel_imp_le` in `Mathlib/Order/Basic.lean`,
/// measured 2026-09-11).
#[test]
fn test_anonymous_instance_binder_keeps_a_dotted_class_name() {
    let code = "example (r : Nat → Nat → Prop) [Std.Refl r] (h : Std.Refl r) : Std.Refl r := h\n";
    let decls = parse_file(code).expect("must parse");
    let SurfaceDecl::Example { binders, .. } = &decls[0] else {
        panic!("expected an example, got {:?}", decls[0]);
    };
    let anon = binders
        .iter()
        .find(|b| matches!(b.info, crate::SurfaceBinderInfo::Instance) && b.name.to_string() == "_")
        .expect("the anonymous instance binder");
    let named = binders
        .iter()
        .find(|b| b.name.to_string() == "h")
        .expect("the named binder");
    // The two types sit at different source positions, so compare them with
    // every `Span { .. }` scrubbed.
    fn without_spans(rendered: &str) -> String {
        let mut out = String::new();
        let mut rest = rendered;
        while let Some(i) = rest.find("Span {") {
            out.push_str(&rest[..i]);
            let after = &rest[i..];
            let j = after.find('}').map_or(after.len(), |j| j + 1);
            rest = &after[j..];
        }
        out.push_str(rest);
        out
    }
    assert_eq!(
        without_spans(&format!("{:?}", anon.ty)),
        without_spans(&format!("{:?}", named.ty)),
        "`[Std.Refl r]` and `(h : Std.Refl r)` must carry the same type expression"
    );
    // Structural, not a Debug-string probe: the head is `Std` projected by
    // the NAMED component `Refl`.
    let head_is_projection_chain = match anon.ty.as_deref() {
        Some(SurfaceExpr::App(_, head, _)) => matches!(
            head.as_ref(),
            SurfaceExpr::Proj(_, base, crate::Projection::Named(field))
                if matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if n.to_string() == "Std")
                    && field.to_string() == "Refl"
        ),
        _ => false,
    };
    assert!(
        head_is_projection_chain,
        "the dotted head must survive as a projection chain, got {:?}",
        anon.ty
    );
}

/// A pattern lambda over several positions is one `fun` per position with a
/// single-arm `match` destructuring each pattern position BEFORE the next
/// position is bound (the shape Lean elaborates), not one lambda over every
/// position followed by the matches. Both spellings — `fun ⟨a, b⟩ ⟨c, d⟩ =>`
/// and the single-arm `fun | ⟨a, b⟩, ⟨c, d⟩ =>` — take it; a multi-arm
/// `fun | …, … => … | …, … => …` keeps the tuple encoding over `_x`.
#[test]
fn test_pattern_lambda_positions_interleave_fun_and_match() {
    fn nest_shape(e: &SurfaceExpr) -> String {
        match e {
            SurfaceExpr::PatternMatchLambda(_, bs, body) | SurfaceExpr::Lambda(_, bs, body) => {
                let names: Vec<String> = bs.iter().map(|b| b.name.to_string()).collect();
                format!("fun {} => {}", names.join(" "), nest_shape(body))
            }
            SurfaceExpr::Match(_, _, scrut, arms) => {
                let SurfaceExpr::Ident(_, s) = scrut.as_ref() else {
                    return "match <non-ident>".to_string();
                };
                let arms: Vec<String> = arms
                    .iter()
                    .map(|a| format!("{:?} => {}", a.pattern, nest_shape(&a.body)))
                    .collect();
                format!("match {s} [{}]", arms.join(" | "))
            }
            SurfaceExpr::Ident(_, n) => n.to_string(),
            other => format!("<{}>", std::any::type_name_of_val(other)),
        }
    }
    for src in ["fun ⟨a, b⟩ ⟨c, d⟩ => a", "fun | ⟨a, b⟩, ⟨c, d⟩ => a"] {
        let e = parse_expr(src).expect("must parse");
        let shape = nest_shape(&e);
        assert!(
            shape.starts_with("fun _dx.0 => match _dx.0 [")
                && shape.contains("fun _dx.1 => match _dx.1 [")
                && shape.ends_with("=> a]]"),
            "{src}: positions must interleave fun/match, got {shape}"
        );
    }
    // A plain variable position is the binder itself, no match.
    let e = parse_expr("fun ⟨a, b⟩ c => a").expect("must parse");
    let shape = nest_shape(&e);
    assert!(
        shape.contains("fun c => a"),
        "a variable position binds directly, got {shape}"
    );
    // Multi-arm lambdas keep the joint tuple match over the (unspellable)
    // pattern-lambda binder `_x.0`.
    let e = parse_expr("fun | 0, 0 => 0 | _, _ => 1").expect("must parse");
    let shape = nest_shape(&e);
    assert!(
        shape.starts_with("fun _x.0 => match _x.0 ["),
        "multi-arm curried lambdas keep the `_x` tuple encoding, got {shape}"
    );
}

/// A superscript-letter postfix operator declared as notation binds to an
/// IDENTIFIER operand exactly as to a parenthesized one: `xᶜ` and `(x 1)ᶜ`
/// both expand through `postfix:1024 "ᶜ" => compl'`. The lexer hands `ᶜ`
/// over as its own token in both positions (it used to be absorbed into `xᶜ`
/// as one identifier, and for one commit could not start a token at all).
#[test]
fn test_superscript_postfix_notation_applies_after_an_identifier() {
    let code = "def compl' (p : Prop) : Prop := ¬ p\n\
                postfix:1024 \"ᶜ\" => compl'\n\
                def a (x : Prop) : Prop := xᶜ\n\
                def b (x : Nat → Prop) : Prop := (x 1)ᶜ\n\
                def c (f : Prop → Prop) (x : Prop) : Prop := f xᶜ\n";
    let decls = parse_file(code).expect("postfix notation and both uses must parse");
    for d in &decls {
        assert!(
            !matches!(d, SurfaceDecl::RawDecl { .. }),
            "no declaration may fall into recovery, got {d:?}"
        );
    }
    let bodies: Vec<String> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } if name.to_string() == "a" || name.to_string() == "b" => {
                Some(format!("{d:?}"))
            }
            _ => None,
        })
        .collect();
    assert_eq!(bodies.len(), 2, "both uses must be defs, got {decls:?}");
    for body in &bodies {
        assert!(
            body.contains("compl'"),
            "the postfix must expand to its notation target, got {body}"
        );
    }
    // `postfix:max` binds to the argument ATOM inside an application:
    // `f xᶜ` is `f (compl' x)`, so the expansion sits under `f`'s argument
    // list — after `f` in the rendering — never around the whole `f x`.
    let c = decls
        .iter()
        .find(|d| matches!(d, SurfaceDecl::Def { name, .. } if name.to_string() == "c"))
        .map(|d| format!("{d:?}"))
        .expect("def c");
    let f_pos = c.find("suffix: [\"f\"]").expect("f applied");
    let compl_pos = c.rfind("suffix: [\"compl'\"]").expect("compl' applied");
    assert!(
        f_pos < compl_pos,
        "`f xᶜ` must parse as `f (compl' x)`, got {c}"
    );
}

/// Attributes parsed before a modifier survive it (`@[simp] private
/// theorem` is Lean's ordinary `declModifiers` order); every modifier arm
/// used to recurse through a fresh attribute read and drop them.
#[test]
fn test_attributes_before_a_modifier_are_kept() {
    let code = "@[simp] private theorem myf_eq (n : Nat) : n = n := rfl\n\
                @[simp, reducible] protected noncomputable def myg (n : Nat) : Nat := n\n";
    let decls = parse_file(code).expect("modifier forms parse");
    let rendered = format!("{decls:?}");
    assert_eq!(decls.len(), 2, "two declarations, got {decls:?}");
    assert!(
        rendered.matches("Simp {").count() == 2 && rendered.contains("Reducible"),
        "the attributes must reach both declarations, got {rendered}"
    );
}

/// `meta def`, `grind_pattern`, a command word after an `attribute` target
/// list, and `rfl` as a declaration name — the four token-table rows
/// measured 2026-09-12 (`Order/Basic.lean:182`, `Logic/Basic.lean:722`,
/// `Data/Subtype.lean:38`, `Logic/Function/Basic.lean:816`).
#[test]
fn test_token_table_command_words_and_rfl_name() {
    let code = "meta def metaNat : Nat := 1\n\
                theorem uses (P : Prop) (h : P) : P := fun _ => h\n\
                grind_pattern Exists.choose_spec => P.choose\n\
                theorem after : True := trivial\n\
                attribute [simp] after\n\
                initialize_simps_projections Subtype (val → coe)\n\
                namespace FactorsThrough\n\
                protected theorem rfl : True := trivial\n\
                end FactorsThrough\n";
    let decls = parse_file(code).expect("the command forms parse");
    let rendered = format!("{decls:?}");
    assert!(
        !rendered.contains("RawDecl"),
        "no declaration may fall into recovery, got {rendered}"
    );
    assert!(
        rendered.contains("metaNat"),
        "`meta def` declares metaNat: {rendered}"
    );
    assert!(
        rendered.contains("\"rfl\""),
        "`protected theorem rfl` is named `rfl`: {rendered}"
    );
}

/// A `postfix:max` operator on an application HEAD binds before the
/// arguments: `xᶜ i` is `(xᶜ) i` (Lean's `app` takes a max-precedence
/// function, `Lean/Parser/Term.lean:853`). The notation term is kept as its
/// own `Paren` unit, the head `elabAppFn` elaborates alone.
#[test]
fn test_max_postfix_binds_to_an_application_head() {
    let code = "def compl' (f : Nat → Prop) : Nat → Prop := fun n => ¬ f n\n\
                postfix:max \"ᶜ\" => compl'\n\
                def d (x : Nat → Prop) (i : Nat) : Prop := xᶜ i\n\
                def e (x : Nat → Prop) : Nat → Prop := xᶜ\n";
    let decls = parse_file(code).expect("a postfix on an application head must parse");
    let val_of = |wanted: &str| {
        decls
            .iter()
            .find_map(|d| match d {
                SurfaceDecl::Def { name, val, .. } if name.to_string() == wanted => {
                    Some(val.as_ref())
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("def {wanted} must parse, got {decls:?}"))
    };
    let SurfaceExpr::App(_, head, args) = val_of("d") else {
        panic!("`xᶜ i` must be an application, got {:?}", val_of("d"));
    };
    assert_eq!(args.len(), 1, "exactly the argument `i`, got {args:?}");
    let SurfaceExpr::Paren(_, inner) = head.as_ref() else {
        panic!("the head must be the notation term `(xᶜ)`, got {head:?}");
    };
    assert!(
        format!("{inner:?}").contains("compl'"),
        "the head is the notation's expansion, got {inner:?}"
    );
    // With nothing applied, the bare notation term comes back unwrapped.
    assert!(
        matches!(val_of("e"), SurfaceExpr::App(..)),
        "`xᶜ` alone is the expansion applied to `x`, got {:?}",
        val_of("e")
    );
}

/// `(e :)` is the type-less ascription, never a parse error, and never the
/// `(e : _)` ascription (whose hole takes the expected type first).
#[test]
fn test_type_ascription_without_type_parses() {
    let expr = parse_expr("(h :)").expect("`(h :)` must parse");
    let SurfaceExpr::App(_, head, args) = &expr else {
        panic!("`(h :)` must be the type-less ascription node, got {expr:?}");
    };
    assert!(
        matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if crate::is_type_ascription_without_type(n)),
        "head must be the type-less ascription marker, got {head:?}"
    );
    assert!(
        matches!(args.as_slice(), [arg] if matches!(&arg.expr, SurfaceExpr::Ident(_, n) if n.to_string() == "h")),
        "the ascribed term is `h`, got {args:?}"
    );
    assert!(
        matches!(parse_expr("(h : _)"), Ok(SurfaceExpr::Ascription(..))),
        "`(h : _)` stays an ordinary ascription"
    );
}
