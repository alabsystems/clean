// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Custom-infix precedence bands — every Lean level parses, and it groups the
//! way Lean groups it.
//!
//! Until this landed the notation registry refused, by design and loudly, any
//! `infix`/`infixl`/`infixr` outside 45–50 and 60+. That covered **92 of
//! Mathlib's 283** infix declarations (33%) — 75 of them below 45, dominated by
//! level 25 with 56 declarations: the whole bundled-morphism surface (`→+`,
//! `→*`, `→+*`, `↪`, `≃`, `≃*`, `≃+*`, `⥤` at 26, `≅` at 10, `⊣`, `→₀`).
//!
//! A parse error is the *safe* failure. The dangerous one is a wrong tree the
//! kernel then accepts, which is what this file pins: every expectation below
//! is the grouping printed by the pinned Lean v4.30.0-rc2 oracle
//! (`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`) under
//! `set_option pp.parens true` with `#check`, transcribed into the same
//! canonical parenthesized-prefix form `precedence_assoc_parity.rs` uses.
//!
//! The rows that most need pinning are the ones where the answer is NOT "the
//! declared level decides": Lean parses `infixl:n` as `term:n op term:(n+1)`
//! and `infixr:n` as `term:(n+1) op term:n`, so at the `→` boundary the two
//! disagree — `A ⋄ B → C` is `(A ⋄ B) → C` for an `infixl:25` but
//! `A ⋄ (B → C)` for an `infixr:25`. Both are recorded below.

use clean_parser::{parse_file, SurfaceArg, SurfaceDecl, SurfaceExpr, SurfaceLit};

/// Canonical parenthesized-prefix rendering, matching
/// `precedence_assoc_parity.rs`: application heads print as the constant the
/// parser emits (`And`, `Iff`, `Prod`, `HAdd.hAdd`, …), `→` prints as
/// `(-> dom cod)`, and parentheses are canonicalized away. Any variant these
/// probes do not expect falls back to `Debug` so an unexpected shape fails
/// loudly instead of silently matching.
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

/// Parse `<decls>\ndef probe := <expr>` and render the value of `probe`.
///
/// A declaration that falls into error recovery panics with the recovered text
/// rather than being silently skipped — "it parsed" is exactly the claim these
/// tests make, so a `RawDecl` must never read as a pass.
fn probe(decls: &str, expr: &str) -> String {
    let code = format!("{decls}\ndef probe := {expr}\n");
    let parsed = parse_file(&code)
        .unwrap_or_else(|e| panic!("`{expr}` (with `{decls}`) should parse the file, got: {e}"));
    for decl in &parsed {
        match decl {
            SurfaceDecl::Def { name, val, .. }
                if name.name() == clean_parser::SurfaceName::generated_path("probe").name() =>
            {
                return render(val)
            }
            SurfaceDecl::RawDecl { content, .. } => panic!(
                "`{expr}` (with `{decls}`) fell into error recovery: {content:?}\n{parsed:#?}"
            ),
            _ => {}
        }
    }
    panic!("no `def probe` in {parsed:#?}");
}

// The named precedences exported by Init.Notation determine the operand
// tree. Lean 4.36.0 and 4.30.0-rc2 agree on all three groupings.
#[test]
fn named_precedences_match_lean_operand_grouping() {
    let decls =
        "infixl:5 \" ⋇ \" => low\ninfixr:min \" ⋈ \" => middle\ninfixr:min1 \" ⋉ \" => high";
    assert_eq!(probe(decls, "a ⋇ b ⋈ c"), "(low a (middle b c))");
    assert_eq!(probe(decls, "a ⋈ b ⋉ c"), "(middle a (high b c))");
    assert_eq!(probe("prefix:lead \"⁂\" => mark", "⁂f x"), "(mark (f x))");
}

// ---------------------------------------------------------------------------
// Every declarable level parses.
//
// The old registry accepted 45–50 and 60+ only; `infixl:25` — 56 Mathlib
// declarations — died with "custom infix operator precedence 25 is outside the
// modeled low (45–50) and arithmetic (60+) bands".
// ---------------------------------------------------------------------------

#[test]
fn test_every_infix_level_0_to_100_parses_and_applies_its_expansion() {
    for level in 0..=100u32 {
        for kind in ["infixl", "infixr", "infix"] {
            let decls = format!("{kind}:{level} \" ⋄ \" => F");
            assert_eq!(
                probe(&decls, "a ⋄ b"),
                "(F a b)",
                "`{kind}:{level}` must parse and lower to its expansion",
            );
        }
    }
}

#[test]
fn test_declared_associativity_holds_in_every_band() {
    // `infixl` left-folds, `infixr` right-nests, at one representative level
    // per band (0–10, 11–20, 21–30, 31–35, 36–50, 51–59, 60+).
    for level in [5u32, 15, 25, 33, 45, 51, 65] {
        assert_eq!(
            probe(&format!("infixl:{level} \" ⋄ \" => F"), "a ⋄ b ⋄ c"),
            "(F (F a b) c)",
            "`infixl:{level}` must left-associate",
        );
        assert_eq!(
            probe(&format!("infixr:{level} \" ⋄ \" => F"), "a ⋄ b ⋄ c"),
            "(F a (F b c))",
            "`infixr:{level}` must right-associate",
        );
    }
}

// ---------------------------------------------------------------------------
// Grouping against the builtin operators, every row transcribed from the
// pinned Lean v4.30.0-rc2 oracle.
//
// `(declarations, expression, expected tree, lean `pp.parens` output)`
// ---------------------------------------------------------------------------

const LEAN_ORACLE: &[(&str, &str, &str, &str)] = &[
    // --- vs `→` (infixr:25). The slot levels decide, not the operator level.
    (
        "infixl:25 \" ⋄ \" => F",
        "A ⋄ B → C",
        "(-> (F A B) C)",
        "(A ⋄b B) → C",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "A ⋄ B → C",
        "(F A (-> B C))",
        "A ⋄c (B → C)",
    ),
    (
        "infix:25 \" ⋄ \" => F",
        "A ⋄ B → C",
        "(-> (F A B) C)",
        "(A ⋄d B) → C",
    ),
    (
        "infixr:26 \" ⋄ \" => F",
        "A ⋄ B → C",
        "(-> (F A B) C)",
        "(A ⋄e B) → C  -- `⥤`, 1128 Mathlib files",
    ),
    (
        "infixr:10 \" ⋄ \" => F",
        "A ⋄ B → C",
        "(F A (-> B C))",
        "A ⋄a (B → C)  -- `≅`, 831 Mathlib files",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "A ⋄ B → C",
        "(-> (F A B) C)",
        "(A ⋄f B) → C",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "A → B ⋄ C",
        "(-> A (F B C))",
        "A → (B ⋄c C)",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "A → B ⋄ C",
        "(-> A (F B C))",
        "A → (B ⋄f C)",
    ),
    // The arrow codomain is `term:25`, so an operator LOOSER than 25 may not be
    // consumed inside it — the `→` closes first.
    (
        "infixr:10 \" ⋄ \" => F",
        "A → B ⋄ C",
        "(F (-> A B) C)",
        "(A → B) ⋄a C",
    ),
    // --- vs `×` (infixr:35) and `⊕` (infixr:30)
    (
        "infixr:25 \" ⋄ \" => F",
        "A ⋄ B × C",
        "(F A (Prod B C))",
        "A ⋄c (B × C)",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "A × B ⋄ C",
        "(F (Prod A B) C)",
        "(A × B) ⋄c C",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "A × B ⋄ C",
        "(Prod A (F B C))",
        "A × (B ⋄f C)",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "A ⋄ B × C",
        "(Prod (F A B) C)",
        "(A ⋄f B) × C",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "A ⋄ B ⊕ C",
        "(F A (Sum B C))",
        "A ⋄c (B ⊕ C)",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "A ⊕ B ⋄ C",
        "(F (Sum A B) C)",
        "(A ⊕ B) ⋄c C",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "A ⊕ B ⋄ C",
        "(Sum A (F B C))",
        "A ⊕ (B ⋄f C)",
    ),
    // --- vs `∧` (infixr:35)
    (
        "infixr:25 \" ⋄ \" => F",
        "p ⋄ q ∧ r",
        "(F p (And q r))",
        "p ⋄c (q ∧ r)",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "p ∧ q ⋄ r",
        "(F (And p q) r)",
        "(p ∧ q) ⋄c r",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "p ∧ q ⋄ r",
        "(And p (F q r))",
        "p ∧ (q ⋄f r)",
    ),
    (
        "infixl:40 \" ⋄ \" => F",
        "p ⋄ q ∧ r",
        "(And (F p q) r)",
        "(p ⋄f q) ∧ r",
    ),
    (
        "infixl:32 \" ⋄ \" => F",
        "p ∧ q ⋄ r",
        "(F (And p q) r)",
        "(p ∧ q) ⋄h r",
    ),
    (
        "infixl:32 \" ⋄ \" => F",
        "p ⋄ q ∧ r",
        "(F p (And q r))",
        "p ⋄h (q ∧ r)",
    ),
    // --- vs `∨` (infixr:30)
    (
        "infixr:25 \" ⋄ \" => F",
        "p ⋄ q ∨ r",
        "(F p (Or q r))",
        "p ⋄c (q ∨ r)",
    ),
    (
        "infixr:25 \" ⋄ \" => F",
        "p ∨ q ⋄ r",
        "(F (Or p q) r)",
        "(p ∨ q) ⋄c r",
    ),
    (
        "infixl:32 \" ⋄ \" => F",
        "p ∨ q ⋄ r",
        "(Or p (F q r))",
        "p ∨ (q ⋄h r)",
    ),
    // --- vs `↔` (infix:20)
    // `↔` (20) binds TIGHTER than a level-15 operator, so it groups first on
    // either side — the mirror image of the level-25 rows above, where `↔` is
    // the looser one.
    (
        "infixr:15 \" ⋄ \" => F",
        "p ↔ q ⋄ r",
        "(F (Iff p q) r)",
        "(p ↔ q) ⋄g r",
    ),
    (
        "infixr:15 \" ⋄ \" => F",
        "p ⋄ q ↔ r",
        "(F p (Iff q r))",
        "p ⋄g (q ↔ r)",
    ),
    (
        "infixr:10 \" ⋄ \" => F",
        "p ↔ q ⋄ r",
        "(F (Iff p q) r)",
        "(p ↔ q) ⋄a r",
    ),
    (
        "infixr:10 \" ⋄ \" => F",
        "p ⋄ q ↔ r",
        "(F p (Iff q r))",
        "p ⋄a (q ↔ r)",
    ),
    (
        "infixr:15 \" ⋄ \" => F",
        "p ⋄ q ∧ r",
        "(F p (And q r))",
        "p ⋄g (q ∧ r)",
    ),
    // --- vs `=` (infix:50) and `+` (infixl:65), the 51–59 band
    (
        "infixl:51 \" ⋄ \" => F",
        "m = n ⋄ k",
        "(Eq m (F n k))",
        "m = (n ⋄i k)",
    ),
    (
        "infixl:51 \" ⋄ \" => F",
        "m ⋄ n = k",
        "(Eq (F m n) k)",
        "(m ⋄i n) = k",
    ),
    (
        "infixl:55 \" ⋄ \" => F",
        "m = n ⋄ k",
        "(Eq m (F n k))",
        "m = (n ⋄j k)",
    ),
    (
        "infixl:55 \" ⋄ \" => F",
        "m ⋄ n = k",
        "(Eq (F m n) k)",
        "(m ⋄j n) = k",
    ),
    (
        "infixl:51 \" ⋄ \" => F",
        "m ⋄ n + k",
        "(F m (HAdd.hAdd n k))",
        "m ⋄i (n + k)",
    ),
    (
        "infixl:51 \" ⋄ \" => F",
        "m + n ⋄ k",
        "(F (HAdd.hAdd m n) k)",
        "(m + n) ⋄i k",
    ),
    // --- two custom operators in different bands
    (
        "infixr:25 \" ⋄ \" => F\ninfixl:40 \" ⍟ \" => G",
        "A ⋄ B ⍟ C",
        "(F A (G B C))",
        "A ⋄c (B ⋄f C)",
    ),
    (
        "infixr:25 \" ⋄ \" => F\ninfixl:40 \" ⍟ \" => G",
        "A ⍟ B ⋄ C",
        "(F (G A B) C)",
        "(A ⋄f B) ⋄c C",
    ),
];

#[test]
fn test_custom_infix_grouping_matches_the_pinned_lean_oracle() {
    let mut wrong = Vec::new();
    for &(decls, expr, expected, lean) in LEAN_ORACLE {
        let got = probe(decls, expr);
        if got != expected {
            wrong.push(format!(
                "  {decls}\n    {expr}\n      lean  {lean}\n      want  {expected}\n      got   {got}"
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} groupings disagree with the pinned Lean v4.30.0-rc2 oracle:\n{}",
        wrong.len(),
        LEAN_ORACLE.len(),
        wrong.join("\n"),
    );
}

// ---------------------------------------------------------------------------
// The Mathlib hom-arrow family, spelled as Mathlib spells it.
// ---------------------------------------------------------------------------

#[test]
fn test_mathlib_hom_arrow_declarations_parse_and_group() {
    // Levels and symbols as declared in mathlib4 (commit 43ad0e9d2):
    // `→+` `Mathlib/Algebra/Group/Hom/Defs.lean` (infixr:25, 285 files),
    // `↪` `Mathlib/Logic/Embedding/Basic.lean:32` (infixr:25, 162 files),
    // `⥤` `Mathlib/CategoryTheory/Functor/Basic.lean:54` (infixr:26, 1128).
    // (Expansion heads are single-segment so the canonical rendering above
    // stays a plain `Ident`; Mathlib's real heads are `AddMonoidHom`,
    // `Function.Embedding` and `CategoryTheory.Functor`.)
    for (decl, sym) in [
        ("infixr:25 \" →+ \" => AddMonoidHom", "→+"),
        ("infixr:25 \" ↪ \" => Embedding", "↪"),
        ("infixr:26 \" ⥤ \" => Functor", "⥤"),
    ] {
        let head = decl.rsplit(" => ").next().expect("decl has an expansion");
        assert_eq!(
            probe(decl, &format!("M {sym} N")),
            format!("({head} M N)"),
            "`{decl}` must parse",
        );
    }

    // `→+` is `infixr:25`, so its right slot is `term:25` and an `→` stays
    // inside it: `M →+ N → P` is `M →+ (N → P)` (pinned oracle).
    assert_eq!(
        probe("infixr:25 \" →+ \" => AddMonoidHom", "M →+ N → P"),
        "(AddMonoidHom M (-> N P))",
    );
    // `⥤` is `infixr:26`, so its right slot is `term:26` and the `→` closes
    // around it: `C ⥤ D → E` is `(C ⥤ D) → E` (pinned oracle).
    assert_eq!(
        probe("infixr:26 \" ⥤ \" => Functor", "C ⥤ D → E"),
        "(-> (Functor C D) E)",
    );
}

// ---------------------------------------------------------------------------
// Postfix precedence and parentheses, measured with Lean 4.36.0.
// ---------------------------------------------------------------------------

#[test]
fn low_postfix_binds_at_its_declared_level() {
    for level in 0..60 {
        let decl = format!("postfix:{level} \" !! \" => Observe");
        assert_eq!(probe(&decl, "p !! !!"), "(Observe (Observe p))");
    }
    for (level, expr, expected) in [
        (0, "a = b !!", "(Observe (Eq a b))"),
        (10, "a |> b !!", "(Observe (b a))"),
        (10, "a !! |> b", "(b (Observe a))"),
        (25, "a → b !!", "(-> a (Observe b))"),
        (25, "a × b !!", "(Observe (Prod a b))"),
        (26, "(a → b) !!", "(Observe (-> a b))"),
        (35, "a ∧ b !!", "(And a (Observe b))"),
        (35, "a × b !!", "(Prod a (Observe b))"),
        (36, "(a × b) !!", "(Observe (Prod a b))"),
        (49, "a = b !!", "(Observe (Eq a b))"),
        (50, "(a !!) = b", "(Eq (Observe a) b)"),
        (51, "a = b !!", "(Eq a (Observe b))"),
        (51, "a !! = b", "(Eq (Observe a) b)"),
        (51, "a + b !!", "(Observe (HAdd.hAdd a b))"),
        (56, "a >>= b !!", "(Bind.bind a (Observe b))"),
        (59, "a ^^^ b !!", "(HXor.hXor a (Observe b))"),
    ] {
        let decl = format!("postfix:{level} \" !! \" => Observe");
        let report =
            clean_parser::parse_file_with_diagnostics(&format!("{decl}\ndef probe := {expr}"))
                .unwrap();
        assert!(
            report.diagnostics.is_empty(),
            "{level} {expr}: {:?}",
            report.diagnostics
        );
        assert_eq!(probe(&decl, expr), expected, "{level} {expr}");
    }
}

#[test]
fn low_postfix_rejects_stronger_trailing_operators_without_parentheses() {
    for (level, expression) in [
        (35, "a !! ∧ b"),
        (49, "a !! = b"),
        (50, "a !! = b"),
        (51, "a !! + b"),
        (49, "a !! ~> b"),
        (49, "a !! ⁇"),
    ] {
        let code = format!("infixl:50 \" ~> \" => And\npostfix:50 \" ⁇ \" => Other\npostfix:{level} \" !! \" => Observe\ndef rejected := {expression}");
        let report = clean_parser::parse_file_with_diagnostics(&code).unwrap();
        assert!(!report.diagnostics.is_empty(), "{level} {expression}");
    }
}

#[test]
fn test_level_50_custom_infix_still_does_not_chain_with_a_comparison() {
    // The relation band keeps Lean's non-associativity at level 50.
    let code = "infixl:50 \" ~> \" => Leads\ndef rejected := a ~> b = c";
    let decls = parse_file(code).expect("file parser should recover");
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Def { name, .. } if name.name() == clean_parser::SurfaceName::generated_path("rejected").name())),
        "a comparison must not chain onto a level-50 custom infix: {decls:#?}",
    );
}
