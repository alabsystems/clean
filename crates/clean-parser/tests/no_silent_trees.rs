// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser Brick 1 — "no silent trees".
//!
//! Guards the invariant introduced by
//! `docs/plans/PARSER_ELAB_DROPIN_AUDIT_2026-07-08.md`: the parser must never
//! FABRICATE a tree for input it does not understand. Every fabrication site
//! catalogued in the audit (P0-2 brace→`Hole`, P0-3 `xs[i]` GetElem, P0-4
//! unknown-infix→`(a _ b)` hole-slot, P0-6 `>>`/`$` operand-drop) must now be a
//! LOUD `ParseError` — a loud gap is strictly better than a silent misparse
//! (task-C guidance). This is the permanent tripwire the audit's §6.3
//! "no-fabrication invariant" specifies; it ships with Brick 1 and would have
//! flagged the entire silent-misparse family automatically.
//!
//! The real parses for these constructs land in Brick 3; this file only locks
//! in the silent→loud conversion.

use std::fmt::Debug;

use clean_parser::{
    parse_expr, parse_file_with_tactics_diagnostics, parse_file_with_tactics_located, ParseReport,
    SurfaceDecl, SurfaceExpr, TacticPatterns,
};

/// Robust "does this tree contain a synthetic placeholder" check.
///
/// Uses the `Debug` rendering so it is immune to `SurfaceExpr` gaining new
/// variants (a structural match would silently miss a new sub-expr carrier).
/// `NamedHole(` is masked first so it does not false-positive on the `Hole(`
/// substring — a `NamedHole` only ever arises from `?name` syntax, which the
/// invariant corpus excludes anyway.
fn debug_has_synthetic_placeholder(value: &impl Debug) -> bool {
    let rendered = format!("{value:?}").replace("NamedHole(", "NamedH0le(");
    rendered.contains("Hole(") || rendered.contains("SyntheticSorry(")
}

fn tree_has_synthetic_placeholder(e: &SurfaceExpr) -> bool {
    debug_has_synthetic_placeholder(e)
}

fn has_named_def(decls: &[SurfaceDecl], expected: &str) -> bool {
    decls
        .iter()
        .any(|decl| matches!(decl, SurfaceDecl::Def { name, .. } if name == expected))
}

/// Exercise both contracts for a recoverable file error:
///
/// - strict parsing must reject the recovery at the authoritative byte;
/// - diagnostic parsing must preserve the following declaration and describe
///   exactly which construct was skipped, without fabricating an AST hole.
fn strict_and_diagnostic_recovery(
    source: &str,
    construct: &str,
    message_fragment: &str,
    recovery_start: usize,
) -> ParseReport {
    let sentinel = source
        .find("def sentinel")
        .expect("every recovery fixture must contain its sentinel declaration");
    let patterns = TacticPatterns::default();

    let strict = parse_file_with_tactics_located(source, &patterns)
        .expect_err("strict parsing must reject every parser recovery");
    assert_eq!(
        strict.byte_offset, recovery_start,
        "strict rejection must report the recovery's authoritative byte for:\n{source}"
    );
    let strict_message = strict.to_string();
    assert!(
        strict_message.contains("strict file parsing rejected recovery `parser.recovery`")
            && strict_message.contains(message_fragment),
        "strict error must retain the structured recovery and root parser error; \
         got: {strict_message}\nsource:\n{source}"
    );

    let report = parse_file_with_tactics_diagnostics(source, &patterns)
        .expect("diagnostic parsing should recover and return the surviving declarations");
    assert_eq!(
        report.diagnostics.len(),
        1,
        "fixture should produce exactly one recovery diagnostic: {:#?}",
        report.diagnostics
    );
    let diagnostic = &report.diagnostics[0];
    assert_eq!(diagnostic.code, "parser.recovery");
    assert_eq!(diagnostic.construct, construct);
    assert_eq!(diagnostic.recovery_start.byte, recovery_start);
    if construct != "error-recovery" {
        let prefix = &source[..recovery_start];
        let expected_line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
        let expected_column = prefix
            .rfind('\n')
            .map_or(recovery_start, |newline| recovery_start - newline - 1);
        assert_eq!(diagnostic.recovery_start.line, expected_line);
        assert_eq!(diagnostic.recovery_start.column, expected_column);
    }
    assert_eq!(diagnostic.recovered_at.byte, sentinel);
    assert_eq!(diagnostic.resumed_token, "Def");
    assert!(
        diagnostic.message.contains(message_fragment),
        "diagnostic must retain `{message_fragment}`, got: {}",
        diagnostic.message
    );
    assert!(
        has_named_def(&report.decls, "sentinel"),
        "recovery swallowed the following declaration: {:#?}",
        report.decls
    );
    assert!(
        !debug_has_synthetic_placeholder(&report.decls),
        "recovery fabricated a Hole/SyntheticSorry declaration tree: {:#?}",
        report.decls
    );
    report
}

/// Brick-3 landing check for the former P0-2 separator-set-builder residual.
/// The parser now lowers `{ x ∈ s | p x }` to the explicit
/// `setOf (fun x => And (Membership.mem s x) (p x))` tree. Keep this in the
/// no-silent-trees suite so a future fallback to either rejection or a
/// fabricated placeholder is loud.
#[test]
fn brick3_separator_set_builder_is_real_not_fabricated() {
    let expr = parse_expr("{ x ∈ s | p x }").expect("separator set-builder should parse");
    assert!(
        !tree_has_synthetic_placeholder(&expr),
        "separator set-builder must not fabricate a placeholder: {expr:?}"
    );
    let rendered = format!("{expr:?}");
    for expected in ["setOf", "Membership.mem", "And"] {
        assert!(
            rendered.contains(expected),
            "separator set-builder must retain `{expected}` in its lowering: {expr:?}"
        );
    }
}

/// Brick-3 landing check for the former P0-4 residual `a ×ˢ b` (set product).
/// `×ˢ` (`SProd.sprod`) is now tokenized as one operator and lowered directly;
/// it must never regress to the old fabricated `Prod a (ˢ b)` application.
#[test]
fn brick3_set_product_superscript_is_real_not_fabricated() {
    let expr = parse_expr("a ×ˢ b").expect("set product should parse");
    assert!(
        !tree_has_synthetic_placeholder(&expr),
        "set product must not fabricate a placeholder: {expr:?}"
    );
    assert!(
        matches!(
            &expr,
            SurfaceExpr::App(_, func, args)
                if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "SProd.sprod")
                    && args.len() == 2
        ),
        "`a ×ˢ b` must lower to the binary SProd.sprod application: {expr:?}"
    );
}

/// The controls: brace / bracket / cdot forms Brick 1 must NOT have broken.
/// These are `_`-free and must parse to Hole-free trees.
const HOLE_FREE_CONTROLS: &[&str] = &[
    // Brace forms Clean genuinely parses.
    "{}",
    "{ x := 1 }",
    "{ x := 1, y := 2 }",
    "{ x | p x }",
    "{ x : Nat | p x }",
    "{ s with x := 1 }",
    // Application to a list literal keeps working WITH a space.
    "xs [i]",
    "f [1, 2, 3]",
    // `·` sections are untouched (only `•` was split out).
    "(· + 1)",
    "f ·",
    // Audit "not-a-bug" list — supported operators, must stay Hole-free.
    "2 + 3 * 4",
    "2 - 3 - 4",
    "2 ^ 3 ^ 2",
    "A → B → C",
    "A × B × C",
    "A ⊕ B ⊕ C",
    "a && b || c",
    "¬ p ∧ q",
    "a :: xs ++ ys",
    "a ∪ b ∩ c",
    // NOTE: bounded quantifiers like `∃ x > 0, p x` are intentionally EXCLUDED:
    // their correct desugaring is `Exists _ (fun x => …)`, where the `_` is a
    // deliberate implicit-domain placeholder — a legitimate `Hole` in a
    // *recognized* construct, not a fabrication for unrecognized input.
    "a >>= f",
    "f <$> x",
    "a <<< b >>> c",
    "m.comap (f) = m",
];

#[test]
fn brick1_no_synthetic_hole_for_hole_free_inputs() {
    for input in HOLE_FREE_CONTROLS {
        match parse_expr(input) {
            Ok(expr) => assert!(
                !tree_has_synthetic_placeholder(&expr),
                "`_`-free input `{input}` must parse to a Hole-free tree, got: {expr:?}"
            ),
            Err(e) => panic!("control input `{input}` should still parse, got error: {e}"),
        }
    }
}

#[test]
fn malformed_definition_equations_are_loud_and_preserve_the_next_declaration() {
    let cases = [
        (
            "def bad : Nat → Nat → Nat\n| 0, y => y\n| x => x\ndef sentinel := 1\n",
            "definition equation arity mismatch: expected 2 pattern(s), found 1",
        ),
        (
            "def bad : Nat → Nat\n| 0 0\ndef sentinel := 1\n",
            "expected FatArrow, got NatLit",
        ),
        (
            "def bad : Nat → Nat\n| 0 =>\ndef sentinel := 1\n",
            "expected definition equation body after `=>`",
        ),
        (
            "def bad : Nat → Nat where\ndef sentinel := 1\n",
            "expected definition equation arm beginning with `|`",
        ),
        (
            "def bad : Nat → Nat\n| . => 0\ndef sentinel := 1\n",
            "expected pattern, got FatArrow",
        ),
        (
            "def bad : Nat → Nat\n| some . => 0\ndef sentinel := 1\n",
            "expected pattern argument, got FatArrow",
        ),
        (
            "def bad : Nat → Nat\n| `foo => 0\ndef sentinel := 1\n",
            "syntax quotation patterns are not supported",
        ),
        (
            "def bad (x : Nat) : Nat := match x with | . => 0\ndef sentinel := 1\n",
            "expected pattern, got FatArrow",
        ),
    ];

    for (source, message) in cases {
        let bad_start = source.find("def bad").expect("fixture has bad declaration");
        let report = strict_and_diagnostic_recovery(source, "error-recovery", message, bad_start);
        assert!(
            !has_named_def(&report.decls, "bad"),
            "a malformed equation must not survive as a real Def: {:#?}",
            report.decls
        );
        assert_eq!(
            report
                .decls
                .iter()
                .filter(|decl| matches!(decl, SurfaceDecl::RawDecl { .. }))
                .count(),
            1,
            "the malformed declaration should be represented by one explicit recovery node"
        );
    }
}

#[test]
fn malformed_termination_hints_are_structured_recoveries_without_holes() {
    let cases = [
        (
            "def bad (n : Nat) : Nat := n\ntermination_by\ndef sentinel := 1\n",
            "termination_by",
            "`termination_by` requires a measure expression",
            "def sentinel",
        ),
        (
            "def bad (n : Nat) : Nat := n\ntermination_by structural\ndef sentinel := 1\n",
            "termination_by",
            "`termination_by structural` requires a parameter name",
            "def sentinel",
        ),
        (
            "def bad (n : Nat) : Nat := n\ntermination_by (\ndef sentinel := 1\n",
            "termination_by",
            "unexpected token: Def",
            "def sentinel",
        ),
        (
            "def bad (n : Nat) : Nat := n\ntermination_by n ( => n\ndef sentinel := 1\n",
            "termination_by",
            "unexpected token: FatArrow",
            "=> n\ndef sentinel",
        ),
        (
            "def bad (n : Nat) : Nat := n\ntermination_by? unexpectedArg\ndef sentinel := 1\n",
            "termination_by",
            "`termination_by?` takes no arguments",
            "unexpectedArg",
        ),
        (
            "def bad (n : Nat) : Nat := n\ndecreasing_by\ndef sentinel := 1\n",
            "decreasing_by",
            "`decreasing_by` requires a non-empty tactic body",
            "def sentinel",
        ),
        (
            "def bad (n : Nat) : Nat := n\ndecreasing_by )\ndef sentinel := 1\n",
            "decreasing_by",
            "`decreasing_by` requires a non-empty tactic body",
            ")\ndef sentinel",
        ),
    ];

    for (source, construct, message, recovery_marker) in cases {
        let recovery_start = source
            .find(recovery_marker)
            .expect("fixture has recovery marker");
        let report = strict_and_diagnostic_recovery(source, construct, message, recovery_start);
        assert!(
            has_named_def(&report.decls, "bad"),
            "a malformed optional hint should not discard its otherwise valid definition"
        );
        assert!(
            !report
                .decls
                .iter()
                .any(|decl| matches!(decl, SurfaceDecl::RawDecl { .. })),
            "hint-local recovery should not degrade the declaration to RawDecl: {:#?}",
            report.decls
        );
        let termination = report
            .decls
            .iter()
            .find_map(|decl| match decl {
                SurfaceDecl::Def {
                    name, termination, ..
                } if name == "bad" => Some(termination),
                _ => None,
            })
            .expect("bad definition must survive");
        if construct == "termination_by" {
            assert!(
                termination.termination_by.is_none(),
                "malformed termination_by must be omitted, not fabricated"
            );
        } else {
            assert!(
                termination.decreasing_by.is_none(),
                "malformed decreasing_by must be omitted, not fabricated"
            );
        }
    }
}

#[test]
fn duplicate_termination_hints_recover_with_progress_and_keep_the_first_hint() {
    let cases = [
        (
            "def bad (n : Nat) : Nat := n\ntermination_by n\ntermination_by duplicateMeasure\ndef sentinel := 1\n",
            "termination_by",
            "duplicate `termination_by` clause",
            "duplicateMeasure",
        ),
        (
            "def bad (n : Nat) : Nat := n\ndecreasing_by simp\ndecreasing_by duplicateTactic\ndef sentinel := 1\n",
            "decreasing_by",
            "duplicate `decreasing_by` clause",
            "duplicateTactic",
        ),
    ];

    for (source, construct, message, recovery_marker) in cases {
        let recovery_start = source
            .find(recovery_marker)
            .expect("fixture has duplicate body marker");
        let report = strict_and_diagnostic_recovery(source, construct, message, recovery_start);
        let termination = report
            .decls
            .iter()
            .find_map(|decl| match decl {
                SurfaceDecl::Def {
                    name, termination, ..
                } if name == "bad" => Some(termination),
                _ => None,
            })
            .expect("definition with first valid hint must survive");
        if construct == "termination_by" {
            assert!(termination.termination_by.is_some());
        } else {
            assert!(termination.decreasing_by.is_some());
        }
    }
}

/// Declaration- and pattern-level controls for the no-fabrication invariant.
/// These inputs intentionally avoid `_`, `?`, and `sorry`; every accepted tree
/// must therefore be free of `Hole` and `SyntheticSorry` at every nesting level.
const HOLE_FREE_DECL_CONTROLS: &[&str] = &[
    "def choose : Nat → Nat → Nat\n| 0, y => y\n| x, y => x\n",
    "def first : Nat × Nat → Nat\n| (x, y) => x\n",
    "def inaccessible : Nat → Nat\n| .(0) => 0\n",
    "def stringTag (s : String) : Nat := match s with | \"x\" => 1 | other => 0\n",
    "def charTag (c : Char) : Nat := match c with | 'x' => 1 | other => 0\n",
    "def leadingDot (x : Option Nat) : Nat := match x with | Option.some .zero => 0 | Option.none => 1\n",
    "def lambdaMeasure (n : Nat) : Nat := n\ntermination_by fun x => x\n",
    "def matchMeasure (n : Nat) : Nat := n\ntermination_by match n with | 0 => 0 | x => x\n",
    "def hintedWhere (n : Nat) : Nat := helper n\ndecreasing_by simp\nwhere\n  helper (x : Nat) : Nat := x\n",
];

#[test]
fn declarations_and_patterns_never_fabricate_placeholders() {
    let patterns = TacticPatterns::default();
    for source in HOLE_FREE_DECL_CONTROLS {
        let decls = parse_file_with_tactics_located(source, &patterns).unwrap_or_else(|err| {
            panic!("control declaration should parse strictly:\n{source}\n{err}")
        });
        assert!(
            !decls
                .iter()
                .any(|decl| matches!(decl, SurfaceDecl::RawDecl { .. })),
            "strict controls must not contain recovery declarations: {decls:#?}"
        );
        assert!(
            !debug_has_synthetic_placeholder(&decls),
            "hole-free declaration control fabricated a placeholder:\n{source}\n{decls:#?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Proptest: the no-fabrication invariant over generated `_`-free expressions.
//
// Generates expressions from a restricted-but-real subset (identifiers, nat
// literals, parens, and a handful of SUPPORTED infix operators) that never
// contains `_`, `?`, or `sorry`. The invariant: whenever such an input parses
// successfully, the tree contains no synthetic `Hole`/`SyntheticSorry`. A
// fabrication site (e.g. a reintroduced unknown-infix hole-slot) would make a
// generated expr parse to a tree carrying a `Hole`, tripping this immediately.
// ---------------------------------------------------------------------------

use proptest::prelude::*;

fn hole_free_expr_strategy() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        prop::sample::select(vec!["a", "b", "c", "f", "g", "x", "y"]).prop_map(String::from),
        (0u32..1000).prop_map(|n| n.to_string()),
    ];
    // Only SUPPORTED infix operators — a well-formed operand pair around any of
    // these always parses to a Hole-free tree.
    let ops = prop::sample::select(vec![
        " + ", " - ", " * ", " ^ ", " = ", " ≤ ", " ∧ ", " ∨ ", " → ", " × ", " ++ ", " :: ",
        " >>= ", " <$> ",
    ]);
    leaf.prop_recursive(4, 32, 4, move |inner| {
        prop_oneof![
            (inner.clone(), ops.clone(), inner.clone())
                .prop_map(|(l, op, r)| format!("{l}{op}{r}")),
            inner.prop_map(|e| format!("({e})")),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn brick1_generated_hole_free_exprs_never_fabricate(input in hole_free_expr_strategy()) {
        // Guard: the generator must not emit a literal `_`/`?`/`sorry`.
        prop_assume!(!input.contains('_') && !input.contains('?') && !input.contains("sorry"));
        if let Ok(expr) = parse_expr(&input) {
            prop_assert!(
                !tree_has_synthetic_placeholder(&expr),
                "no-fabrication invariant violated: `{}` parsed to a tree with a synthetic \
                 placeholder: {:?}",
                input,
                expr
            );
        }
    }
}
