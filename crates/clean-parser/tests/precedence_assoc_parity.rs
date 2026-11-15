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
        SurfaceExpr::Ident(_, s) => s
            .source_spelling()
            .expect("fixture identifier has exact source spelling"),
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
// There is NO prefix `+` in Lean, and pretending otherwise silently rewrites
// Mathlib's `→+`.
//
// `neg_expr` used to carry a `TokenKind::Plus` arm commented "unary plus is a
// no-op": it consumed the `+` and returned the operand unchanged. That is not
// a harmless leniency. The pinned v4.30.0-rc2 toolchain declares no
// `prefix "+"` anywhere in `Init` and rejects every row below at PARSE time
// with `unexpected token '+'; expected term`, so accepting `+e ≡ e` makes
// `A →+ B` — Mathlib's `AddMonoidHom` notation, **996 lines across 285 files**
// of mathlib4 `43ad0e9d2` — parse as `A → (+ B)` ≡ `A → B`, a plain function
// arrow. The resulting term is well-formed, elaborates, and is ACCEPTED by the
// kernel, so a theorem stated about a bundled monoid hom gets kernel-verified
// against a different proposition with no diagnostic anywhere. Every sibling in
// the family (`→+*`, `→*`, `→₀`, `→ₗ`, `→ₐ`, `≃o`, `≃*`, `≃+`) already failed
// loudly; `→+` was silent only because `+` alone had a prefix rule.
//
// `offending` is the fragment Clean's diagnostic must name, so a future
// "recovery" that swallows the `+` again cannot pass this test quietly.
// ---------------------------------------------------------------------------
const NO_PREFIX_PLUS: &[(&str, &str, &str)] = &[
    (
        "+ B",
        "+",
        "lean 4.30.0-rc2: `#check + B` -> error: unexpected token '+'; expected term",
    ),
    (
        "+3",
        "+",
        "lean 4.30.0-rc2: `#check +3` -> error: unexpected token '+'; expected term",
    ),
    (
        "1 + + 2",
        "+",
        "lean 4.30.0-rc2: `#check 1 + + 2` -> error: unexpected token '+'; expected term",
    ),
    (
        // The reason this arm mattered: the hom-arrow family.
        "A →+ B",
        "+",
        "lean 4.30.0-rc2: `#check (A →+ B)` -> error: unexpected token '+'; expected term",
    ),
    (
        "(A →+ B) = (A → B)",
        "+",
        "lean 4.30.0-rc2: same rejection inside an equation",
    ),
];

#[test]
fn no_prefix_plus_hom_arrow_is_loud() {
    for (input, offending, oracle) in NO_PREFIX_PLUS {
        match parse_expr(input) {
            Err(e) => {
                let rendered = e.to_string();
                assert!(
                    rendered.contains(offending),
                    "`{input}` must name `{offending}` in its diagnostic \
                     (Lean oracle: {oracle}), got: {rendered}"
                );
            }
            Ok(tree) => panic!(
                "`{input}` must be a loud ParseError — Lean has no prefix `+` \
                 ({oracle}); accepting it silently degrades `→+` to `→`. Got: {}",
                render(&tree)
            ),
        }
    }
}

/// Control: deleting the prefix-`+` arm must not touch BINARY `+`, nor the
/// prefix `-` that shares `neg_expr`, nor `++`.
#[test]
fn no_prefix_plus_controls_unchanged() {
    for (input, expected) in [
        ("a + b", "(HAdd.hAdd a b)"),
        ("a + -b", "(HAdd.hAdd a (Neg.neg b))"),
        ("-a + b", "(HAdd.hAdd (Neg.neg a) b)"),
        ("a * b + c", "(HAdd.hAdd (HMul.hMul a b) c)"),
        ("xs ++ ys", "(HAppend.hAppend xs ys)"),
        ("a → b", "(-> a b)"),
    ] {
        assert_eq!(
            render_parsed(input),
            expected,
            "control `{input}` regressed when the prefix-`+` arm was deleted"
        );
    }
}

/// Lean's tactic `optConfig` — `simp +contextual`, `simp +arith only [h]`,
/// `decide +kernel` — owns its own `+`, and must keep working now that the
/// term grammar rejects one.
///
/// Measured on mathlib4 `43ad0e9d2`: **832 sites** (767 `simp`, 38 `decide`,
/// 19 `grind`, 8 `simp_all`). They used to reach the TERM grammar, where the
/// no-op prefix `+` quietly turned `+contextual` into the term `contextual`;
/// deleting that prefix without giving the tactic grammar its own rule turned
/// all 832 into recovery diagnostics (caught by re-running the 40-module
/// Mathlib parse sweep, which lost `Mathlib.Topology.Constructions`'s
/// `simp +unfoldPartialApp [...]` at line 882).
#[test]
fn tactic_config_options_survive_the_prefix_plus_deletion() {
    use clean_parser::parse_file;
    for src in [
        "theorem t (a : Nat) : a = a := by simp +contextual\n",
        "theorem t (a : Nat) : a = a := by simp +arith only [Nat.add_comm]\n",
        "theorem t (a : Nat) : a = a := by simp +contextual +instances [Nat.le_refl]\n",
        "theorem t (a : Nat) : a = a := by simp +unfoldPartialApp [Nat.le_refl]\n",
        "theorem t (a : Nat) : a = a := by decide +kernel\n",
        "theorem t (a : Nat) : a = a := by simp_all +contextual\n",
    ] {
        let decls = parse_file(src).unwrap_or_else(|e| panic!("`{src}` should parse, got: {e}"));
        assert!(
            !decls
                .iter()
                .any(|d| matches!(d, clean_parser::SurfaceDecl::RawDecl { .. })),
            "tactic config in `{src}` must not degrade to error recovery: {decls:#?}"
        );
    }
}

/// Control: the config rule must not swallow a `+` that is NOT a config
/// option. `simp [a + b]` and `omega` after a `+` term are untouched, and a
/// bare `+` with no option name is still the loud term-position error.
#[test]
fn tactic_config_rule_does_not_eat_arithmetic() {
    use clean_parser::parse_file;
    let src = "theorem t (a b : Nat) : a + b = b + a := by simp [Nat.add_comm a b]\n";
    let decls = parse_file(src).expect("ordinary simp lemma list should parse");
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, clean_parser::SurfaceDecl::RawDecl { .. })),
        "an ordinary `simp [..]` must be unaffected: {decls:#?}"
    );
    // `+ 3` is not `+ident`, so it stays a term-position error.
    assert!(
        parse_expr("+ 3").is_err(),
        "the config rule is tactic-local; `+ 3` in a term must still be loud"
    );
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
