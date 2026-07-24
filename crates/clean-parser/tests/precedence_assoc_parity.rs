// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser Brick 2 — precedence & associativity parity.
//!
//! The two families Brick 1 ("no silent trees") does NOT catch, because they
//! parse to well-formed but WRONG trees that even typecheck — the kernel
//! re-check cannot flag them (`docs/plans/PARSER_ELAB_DROPIN_AUDIT_2026-07-08.md`
//! §5 Brick 2):
//!
//! * **P0-1** — unary minus vs `^`. Lean: `-` is `prefix:75`
//!   (`Init/Notation.lean:293`), `^` is `infixr:80` (`Init/Notation.lean:291`),
//!   `*` is `infixl:70`. So `-3 ^ 2` = `-(3 ^ 2)` = **-9** and `-3 * 2` =
//!   `(-3) * 2` = **-6**. Clean historically put the prefix minus at the BOTTOM
//!   of the precedence chain (below `^`), silently parsing `(-3) ^ 2` = **9**.
//!
//! * **P0-5** — non-associative comparison / equality chains. Lean declares
//!   `=`, `≠`, `!=`, `<`, `≤`, `>`, `≥`, `==`, `≍`, `∈`, `∉`, `⊆`, `⊂` all
//!   `infix:50` (non-chaining), so `a = b = c`, even mixed `a < b = c`, are
//!   PARSE ERRORS. Clean silently folded them left-associatively.
//!
//! Every row is grounded on the pinned Lean v4.30.0-rc2 oracle
//! (`set_option pp.parens true in #check <e>` for trees, `#eval <e>` for
//! values). Trees are rendered into the audit's normalized parenthesized-prefix
//! form (desugared heads shown, e.g. `+` → `HAdd.hAdd`) and compared exactly —
//! the parse-tree parity the success/failure gates cannot express (audit §6).

use clean_parser::{parse_expr, ParseError, SurfaceArg, SurfaceExpr, SurfaceLit};

/// Canonical parenthesized-prefix rendering of a `SurfaceExpr`, matching the
/// audit's tree notation. Application heads print as their desugared constant
/// (`Neg.neg`, `HPow.hPow`, …) exactly as the parser emits them; `→` prints as
/// `(-> dom cod)`; parentheses are transparent (canonicalized away). Any variant
/// not expected in these arithmetic/relation probes falls back to `Debug`, which
/// makes an unexpected shape fail loudly rather than silently pass.
fn render(e: &SurfaceExpr) -> String {
    match e {
        SurfaceExpr::Ident(_, s) => s.clone(),
        SurfaceExpr::Lit(_, SurfaceLit::Nat(n)) => n.to_string(),
        SurfaceExpr::Paren(_, inner) => render(inner),
        SurfaceExpr::App(_, f, args) => {
            let mut parts = vec![render(f)];
            parts.extend(args.iter().map(|a: &SurfaceArg| render(&a.expr)));
            format!("({})", parts.join(" "))
        }
        SurfaceExpr::Arrow(_, dom, cod) => format!("(-> {} {})", render(dom), render(cod)),
        other => format!("{other:?}"),
    }
}

fn render_parsed(input: &str) -> String {
    render(&parse_expr(input).unwrap_or_else(|e| panic!("`{input}` should parse, got: {e}")))
}

// ---------------------------------------------------------------------------
// P0-1 — unary minus precedence (`prefix:75`, between `*` 70 and `^` 80).
//
// `(input, expected_canonical_tree, lean_oracle)`. Every expected tree is the
// `pp.parens` parse Lean v4.30 produces; the `lean_oracle` column records the
// `#eval` value or the `#check` shape that grounds it.
// ---------------------------------------------------------------------------
const NEG_PRECEDENCE: &[(&str, &str, &str)] = &[
    (
        "-3 ^ 2",
        "(Neg.neg (HPow.hPow 3 2))",
        "#eval (-3 ^ 2 : Int) = -9  (Clean previously gave 9)",
    ),
    (
        "-3 * 2",
        "(HMul.hMul (Neg.neg 3) 2)",
        "#eval (-3 * 2 : Int) = -6  (neg binds tighter than *)",
    ),
    (
        "-3 + 2",
        "(HAdd.hAdd (Neg.neg 3) 2)",
        "#eval (-3 + 2 : Int) = -1",
    ),
    (
        "-2 ^ 2 ^ 3",
        "(Neg.neg (HPow.hPow 2 (HPow.hPow 2 3)))",
        "#eval (-2 ^ 2 ^ 3 : Int) = -256  (^ right-assoc, under neg)",
    ),
    (
        "- -3",
        "(Neg.neg (Neg.neg 3))",
        "#eval (- -3 : Int) = 3  (nested prefix neg)",
    ),
    (
        "-a * -b",
        "(HMul.hMul (Neg.neg a) (Neg.neg b))",
        "#check `-a * -b` = `(-a) * (-b)`",
    ),
    (
        "-a ^ 2 + b",
        "(HAdd.hAdd (Neg.neg (HPow.hPow a 2)) b)",
        "#check `-a ^ 2 + b` = `(-(a ^ 2)) + b`",
    ),
    (
        "2 * -3",
        "(HMul.hMul 2 (Neg.neg 3))",
        "#check `2 * -3` = `2 * (-3)`  (mul right operand admits neg)",
    ),
];

#[test]
fn brick2_neg_precedence_matches_lean() {
    for (input, expected, oracle) in NEG_PRECEDENCE {
        let got = render_parsed(input);
        assert_eq!(
            &got, expected,
            "neg-precedence divergence for `{input}` (Lean oracle: {oracle})"
        );
    }
}

/// `2 ^ -3` is a PARSE ERROR in Lean v4.30 ("unexpected token at this precedence
/// level; consider parenthesizing the term") because `^`'s right operand is
/// parsed at prec 80 and `-` is only `prefix:75`; the fix must reproduce that
/// rejection rather than silently accept `2 ^ (-3)`. Same for `a ^ -b`.
#[test]
fn brick2_neg_below_pow_right_operand_is_loud() {
    for input in ["2 ^ -3", "a ^ -b", "-3 ^ -2"] {
        assert!(
            matches!(parse_expr(input), Err(ParseError::UnexpectedToken { .. })),
            "`{input}` must be a loud ParseError (Lean rejects it; use parens), got: {:?}",
            parse_expr(input)
        );
    }
}

// ---------------------------------------------------------------------------
// P0-5 — non-associative comparison/equality chains (all `infix:50`).
//
// Each row is a chain Lean v4.30 REJECTS with "unexpected token '<op>'; expected
// command". `offending_op` is the second operator (the one Lean's parser trips
// on) — it must appear in Clean's loud diagnostic.
// ---------------------------------------------------------------------------
const REJECTED_CHAINS: &[(&str, &str)] = &[
    ("a = b = c", "="),
    ("a < b < c", "<"),
    ("a ≤ b ≤ c", "≤"),
    ("a > b > c", ">"),
    ("a ≥ b ≥ c", "≥"),
    ("a ≠ b ≠ c", "≠"),
    ("a == b == c", "=="),
    ("a != b != c", "!="),
    // MIXED 50-class operators are rejected too (Lean: `a < b = c` errors).
    ("a < b = c", "="),
    ("a = b < c", "<"),
    ("a ≤ b < c", "<"),
    // Membership / subset relations are `notation:50 … :50` / `infix:50`.
    ("xs ⊆ ys ⊆ zs", "⊆"),
    ("s ⊂ t ⊂ u", "⊂"),
];

#[test]
fn brick2_comparison_chains_are_loud() {
    for (input, offending) in REJECTED_CHAINS {
        match parse_expr(input) {
            Err(ParseError::UnexpectedToken { message, .. }) => {
                assert!(
                    message.contains("not associative"),
                    "`{input}` must report a non-associativity error, got: {message}"
                );
                assert!(
                    message.contains(offending),
                    "`{input}` diagnostic should name the offending `{offending}`, got: {message}"
                );
            }
            other => panic!(
                "chain `{input}` must be a loud ParseError (Lean rejects it), got: {other:?}"
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Controls — shapes the precedence/assoc changes must NOT have broken. Every
// expected tree is the Lean v4.30 `pp.parens` parse.
// ---------------------------------------------------------------------------
const PARITY_CONTROLS: &[(&str, &str, &str)] = &[
    // A single comparison still parses (loop runs exactly once).
    ("a = b", "(Eq a b)", "#check a = b"),
    ("a < b", "(LT.lt a b)", "#check a < b"),
    ("a ≤ b", "(LE.le a b)", "#check a ≤ b"),
    // Parenthesizing one side makes a "chain" legal in Lean — and here.
    (
        "(a = b) = c",
        "(Eq (Eq a b) c)",
        "#check (a = b) = c  (Prop)",
    ),
    // A looser operator between comparisons is fine (different chain level).
    (
        "a + b = c",
        "(Eq (HAdd.hAdd a b) c)",
        "#check a + b = c = (a+b)=c",
    ),
    (
        "a = b + c",
        "(Eq a (HAdd.hAdd b c))",
        "#check a = b + c = a=(b+c)",
    ),
    // The `=` arrow-tail re-association is preserved: `→` (prec 25) is looser.
    ("a = b → c", "(-> (Eq a b) c)", "#check a = b → c = (a=b)→c"),
    (
        "a = b → c = d",
        "(-> (Eq a b) (Eq c d))",
        "#check a = b → c = d = (a=b)→(c=d)",
    ),
    // Right-associative `^` unaffected.
    (
        "2 ^ 3 ^ 2",
        "(HPow.hPow 2 (HPow.hPow 3 2))",
        "#check 2 ^ 3 ^ 2  (infixr:80)",
    ),
];

#[test]
fn brick2_parity_controls_unchanged() {
    for (input, expected, oracle) in PARITY_CONTROLS {
        let got = render_parsed(input);
        assert_eq!(
            &got, expected,
            "control `{input}` regressed (Lean oracle: {oracle})"
        );
    }
}
