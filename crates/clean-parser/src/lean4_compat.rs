// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 Parser Compatibility Tests
//!
//! This module tests clean parser against actual Lean 4 test files
//! to measure and track compatibility percentage.

#[cfg(test)]
mod tests {
    use crate::Parser;
    use std::borrow::Cow;
    use std::fs;
    use std::path::Path;
    use std::sync::mpsc;
    use std::sync::mpsc::RecvTimeoutError;
    use std::time::Duration;
    use walkdir::WalkDir;

    const PARSER_COMPAT_TIMEOUT: Duration = Duration::from_secs(10);

    fn parser_compat_error(message: impl Into<String>) -> crate::ParseError {
        crate::ParseError::UnexpectedToken {
            line: 0,
            col: 0,
            message: message.into(),
        }
    }

    fn parse_with_small_stack_timeout(content: String) -> Result<(), crate::ParseError> {
        let (tx, rx) = mpsc::channel();
        let handle = std::thread::Builder::new()
            .stack_size(clean_kernel::test_utils::SMALL_STACK)
            .spawn(move || {
                let result = Parser::parse_file(&content).map(|_| ());
                let _ = tx.send(result);
            })
            .map_err(|err| parser_compat_error(format!("Parser thread spawn failed: {err}")))?;

        match rx.recv_timeout(PARSER_COMPAT_TIMEOUT) {
            Ok(result) => {
                let _ = handle.join();
                result
            }
            Err(RecvTimeoutError::Timeout) => Err(parser_compat_error(format!(
                "Parser timed out after {}s",
                PARSER_COMPAT_TIMEOUT.as_secs()
            ))),
            Err(RecvTimeoutError::Disconnected) => {
                let detail = match handle.join() {
                    Ok(()) => "Parser thread disconnected before reporting results".to_string(),
                    Err(_) => "Parser thread panicked (possible stack overflow)".to_string(),
                };
                Err(parser_compat_error(detail))
            }
        }
    }

    /// Test parsing of Lean 4 test suite files
    /// Reports compatibility percentage for tracking
    #[test]
    fn lean4_parser_compatibility_suite() {
        // Path relative to crate root (crates/clean-parser/)
        let test_dir = Path::new("../../tests/lean4_compat/lean4_tests");

        if !test_dir.exists() {
            println!("Lean 4 test files not found at {test_dir:?}");
            println!("Run scripts/lean4_compat/download_tests.sh to download test files");
            return;
        }

        let mut passed = 0;
        let mut failed = 0;
        let mut failures: Vec<(String, String)> = Vec::new();

        for entry in WalkDir::new(test_dir)
            .into_iter()
            .filter_map(Result::ok)
            .filter(|e| e.path().extension().is_some_and(|ext| ext == "lean"))
        {
            let path = entry.path();
            let (content, lossy_utf8) = match fs::read(path) {
                Ok(bytes) => match String::from_utf8_lossy(&bytes) {
                    Cow::Owned(s) => (s, true),
                    Cow::Borrowed(s) => (s.to_string(), false),
                },
                Err(e) => {
                    failed += 1;
                    failures.push((path.display().to_string(), format!("IO error: {e}")));
                    continue;
                }
            };

            // Parse in a separate thread with limited stack to detect stack overflow
            let filename = path
                .file_name()
                .map(|n| n.to_string_lossy().to_string())
                .unwrap_or_default();
            eprint!("Parsing: {filename}... ");
            let result = parse_with_small_stack_timeout(content);
            eprintln!("done");

            match result {
                Ok(_) => passed += 1,
                Err(e) => {
                    failed += 1;
                    let mut msg = format!("{e}");
                    if lossy_utf8 {
                        msg.push_str(" [lossy utf-8 decode]");
                    }
                    failures.push((path.display().to_string(), msg));
                }
            }
        }

        let total = passed + failed;
        let percentage = if total > 0 {
            100.0 * passed as f64 / total as f64
        } else {
            0.0
        };

        println!();
        println!("========================================");
        println!("Lean 4 Parser Compatibility Report");
        println!("========================================");
        println!("Passed: {passed}");
        println!("Failed: {failed}");
        println!("Total:  {total}");
        println!("Compatibility: {percentage:.1}% ({passed}/{total})");
        println!("========================================");

        // Report first 20 failures for debugging
        if !failures.is_empty() {
            println!();
            println!("First {} failures:", failures.len().min(20));
            for (path, err) in failures.iter().take(20) {
                let filename = Path::new(path)
                    .file_name()
                    .map(|n| n.to_string_lossy())
                    .unwrap_or_default();
                // Truncate error to first line
                let short_err = err.lines().next().unwrap_or(err);
                println!("  {filename} - {short_err}");
            }
        }

        // Regression threshold: fail if compatibility drops below baseline
        // Current baseline: 90% (90/100) as of 2026-01-28
        // Update this threshold when parser improvements increase compatibility
        const MIN_COMPATIBILITY_PCT: f64 = 85.0; // Allow 5% buffer below current 90%
        assert!(
            percentage >= MIN_COMPATIBILITY_PCT,
            "Parser compatibility regression: {:.1}% < {:.1}% threshold (passed {}/{})",
            percentage,
            MIN_COMPATIBILITY_PCT,
            passed,
            total
        );
    }

    #[test]
    fn parser_compat_timeout_helper_accepts_simple_file() {
        let result = parse_with_small_stack_timeout("def ok : Nat := 1".to_string());

        assert!(
            result.is_ok(),
            "parser compatibility timeout helper should parse a simple file: {result:?}"
        );
    }

    /// Test specific Lean 4 syntax constructs
    /// These tests track progress - they pass and print status, not panic
    mod specific_constructs {
        use crate::{parse_decl, parse_expr, parse_file};

        fn track(name: &str, result: Result<impl std::fmt::Debug, impl std::fmt::Debug>) -> bool {
            match &result {
                Ok(_) => {
                    println!("✓ {name}");
                    true
                }
                Err(e) => {
                    println!("✗ {name} - {e:?}");
                    false
                }
            }
        }

        #[test]
        fn lean4_syntax_compatibility_summary() {
            let mut passed = 0;
            let mut total = 0;

            // Class definition
            total += 1;
            if track("class definition", parse_decl("class Vec (X : Type u)")) {
                passed += 1;
            }

            // Instance with priority
            total += 1;
            if track(
                "instance with priority",
                parse_decl("instance (priority := default+1) instFoo : Vec ℝ := sorry"),
            ) {
                passed += 1;
            }

            // Structure
            total += 1;
            if track(
                "structure",
                parse_decl("structure Point where\n  x : Nat\n  y : Nat"),
            ) {
                passed += 1;
            }

            // Inductive
            total += 1;
            if track(
                "inductive",
                parse_decl(
                    "inductive List (α : Type u) where\n  | nil : List α\n  | cons : α → List α → List α",
                ),
            ) {
                passed += 1;
            }

            // Theorem
            total += 1;
            if track("theorem", parse_decl("theorem foo : 1 + 1 = 2 := rfl")) {
                passed += 1;
            }

            // do notation
            total += 1;
            if track(
                "do notation",
                parse_decl("def test : IO Unit := do\n  let x ← pure 1\n  pure ()"),
            ) {
                passed += 1;
            }

            // match expression
            total += 1;
            if track(
                "match expression",
                parse_decl(
                    "def foo (n : Nat) : Nat :=\n  match n with\n  | 0 => 1\n  | n + 1 => n",
                ),
            ) {
                passed += 1;
            }

            // Lambda with type
            total += 1;
            if track("lambda with type", parse_expr("fun (x : Nat) => x + 1")) {
                passed += 1;
            }

            // Forall type
            total += 1;
            if track("forall type", parse_expr("∀ (x : Nat), x = x")) {
                passed += 1;
            }

            // Implicit binder
            total += 1;
            if track(
                "implicit binder",
                parse_decl("def id {α : Type} (x : α) : α := x"),
            ) {
                passed += 1;
            }

            // Instance implicit
            total += 1;
            if track(
                "instance implicit",
                parse_decl("def toString [ToString α] (x : α) : String := ToString.toString x"),
            ) {
                passed += 1;
            }

            // Namespace
            total += 1;
            if track(
                "namespace",
                parse_file("namespace Foo\ndef bar : Nat := 1\nend Foo"),
            ) {
                passed += 1;
            }

            // Attributes
            total += 1;
            if track("attributes", parse_decl("@[simp] def foo : Nat := 1")) {
                passed += 1;
            }

            // Where clause
            total += 1;
            if track(
                "where clause",
                parse_decl("def foo : Nat → Nat where\n  | 0 => 1\n  | n + 1 => foo n"),
            ) {
                passed += 1;
            }

            // If-then-else
            total += 1;
            if track("if-then-else", parse_expr("if true then 1 else 0")) {
                passed += 1;
            }

            // Let-in
            total += 1;
            if track("let-in", parse_expr("let x := 1; x + 1")) {
                passed += 1;
            }

            // Universe
            total += 1;
            if track(
                "universe command",
                parse_file("universe u v\ndef foo : Type u → Type v := sorry"),
            ) {
                passed += 1;
            }

            // Open/import
            total += 1;
            if track("open command", parse_file("open Nat in #check succ")) {
                passed += 1;
            }

            println!();
            println!("========================================");
            println!("Lean 4 Syntax Construct Compatibility");
            println!("========================================");
            println!(
                "Passed: {}/{} ({:.1}%)",
                passed,
                total,
                100.0 * passed as f64 / total as f64
            );
            println!("========================================");

            // Regression threshold: all core constructs should pass
            // Current baseline: 18/18 (100%) as of 2026-01-28
            const MIN_CONSTRUCTS: usize = 18;
            assert!(
                passed >= MIN_CONSTRUCTS,
                "Syntax construct regression: {} < {} passing constructs",
                passed,
                MIN_CONSTRUCTS
            );
        }

        #[test]
        fn anonymous_constructor_syntax() {
            // Test .foo anonymous constructor syntax
            let result = parse_expr(".done");
            assert!(result.is_ok(), "Failed to parse .done: {result:?}");

            // Test .foo with arguments
            let result = parse_expr(".left c");
            assert!(result.is_ok(), "Failed to parse .left c: {result:?}");

            // Test nested (.foo expr)
            let result = parse_expr("(.left c)");
            assert!(result.is_ok(), "Failed to parse (.left c): {result:?}");

            println!("Anonymous constructor tests passed");
        }

        // Note: test_file_1616_anonymous_ctor is disabled because it requires
        // support for multi-name binders with shared type like (x y z : List α)
        // which is tracked as a separate parser compatibility issue.

        #[test]
        fn test_let_with_explicit_in() {
            // Test let bindings with explicit `in` separator (required without layout sensitivity)
            let code = r"def test : Nat :=
  let x := 1 in
  let y := 2 in
  x + y";
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "Failed to parse let with explicit in: {result:?}"
            );
            println!("Let with explicit in parsed successfully");
        }

        #[test]
        fn test_chained_let_bindings() {
            // Chained let bindings work when the next statement is `let`
            // (no ambiguity about where value ends)
            let code = r"def test : Nat :=
  let x := 1
  let y := 2 in
  x + y";
            let result = parse_file(code);
            assert!(result.is_ok(), "Failed to parse chained let: {result:?}");
            println!("Chained let bindings parsed successfully");
        }

        #[test]
        fn test_let_followed_by_paren_body() {
            // Simple case: let binding followed by parenthesized body
            let code = r"def test : Nat :=
  let x := 1
  (x)";
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "Failed to parse let followed by paren body: {result:?}"
            );
        }

        #[test]
        fn test_let_in_theorem_type_simple() {
            // Let binding in theorem type followed by parenthesized body
            let code = r"theorem test (x : Real) :
  let y := x
  (y = 1) := by sorry";
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "Failed to parse let in theorem type: {result:?}"
            );
        }

        /// MATP-BENCH Q3 let pattern in theorem types - tracked in #105
        #[test]
        fn test_matp_bench_q3_let_pattern() {
            // MATP-BENCH Q3 uses chained let bindings in theorem type annotation
            // This is the problematic pattern: let bindings inside a theorem type
            let code = r#"theorem pentagonAngleH (x : Real) :
  let angleE := x
  let angleF := x + 20
  let angleG := x + 5
  let angleH := x - 5
  let angleJ := x + 10
  (angleE + angleF + angleG + angleH + angleJ = 540) ->
  angleH = 97 := by sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "Failed to parse MATP-BENCH Q3 pattern: {result:?}"
            );
        }

        #[test]
        fn test_bounded_forall_membership() {
            let expr = parse_expr("∀ p ∈ S, P p");
            assert!(
                expr.is_ok(),
                "Failed to parse bounded ∀ membership: {expr:?}"
            );
        }

        #[test]
        fn test_bounded_forall_comparison() {
            let expr = parse_expr("∀ n > 0, P n");
            assert!(
                expr.is_ok(),
                "Failed to parse bounded ∀ comparison: {expr:?}"
            );
        }

        #[test]
        fn test_bounded_exists_membership() {
            let expr = parse_expr("∃ p ∈ S, P p");
            assert!(
                expr.is_ok(),
                "Failed to parse bounded ∃ membership: {expr:?}"
            );
        }

        #[test]
        fn test_bounded_exists_comparison() {
            let expr = parse_expr("∃ n > 0, P n");
            assert!(
                expr.is_ok(),
                "Failed to parse bounded ∃ comparison: {expr:?}"
            );
        }

        // ── Parenthesized bounded binders MUST preserve the guard ────────────
        //
        // Regression for the DEFECT-2 desugar bug: `explicit_binders` parsed a
        // parenthesized bounded binder `(x ∈ s)` / `(n > 0)` and then THREW THE
        // GUARD AWAY, so `∀ (x ∈ s), p` silently became the strictly stronger
        // `∀ x, p` (and `∃ (x ∈ s), p` became `∃ x, p`) — a soundness-relevant
        // meaning change. Lean desugars these to `∀ x, x ∈ s → p` and
        // `∃ x, x ∈ s ∧ p`; these tests assert the guard survives the parse.
        //
        // The assertions inspect the AST directly (not `is_ok`) because a
        // dropped guard still parses successfully — only the shape reveals it.
        use crate::surface::SurfaceExpr;

        /// Count occurrences of `Ident(name)` anywhere in a surface expression.
        fn count_ident(expr: &SurfaceExpr, name: &str) -> usize {
            let here = matches!(expr, SurfaceExpr::Ident(_, s) if s == name) as usize;
            let mut n = here;
            match expr {
                SurfaceExpr::App(_, f, args) => {
                    n += count_ident(f, name);
                    for a in args {
                        n += count_ident(&a.expr, name);
                    }
                }
                SurfaceExpr::Arrow(_, l, r) => {
                    n += count_ident(l, name) + count_ident(r, name);
                }
                SurfaceExpr::Pi(_, _, body) | SurfaceExpr::Lambda(_, _, body) => {
                    n += count_ident(body, name);
                }
                _ => {}
            }
            n
        }

        #[test]
        fn test_paren_bounded_forall_membership_preserves_guard() {
            // `∀ (x ∈ s), P x`  ≡  `∀ x, x ∈ s → P x`
            let expr = parse_expr("∀ (x ∈ s), P x").expect("parenthesized bounded ∀ should parse");
            // Guard desugars to `Membership.mem s x`, wrapped as an Arrow.
            assert!(
                matches!(&expr, SurfaceExpr::Pi(_, _, body) if matches!(&**body, SurfaceExpr::Arrow(..))),
                "∀ (x ∈ s), P x must desugar to a Pi over an Arrow (guard preserved), got {expr:?}"
            );
            assert_eq!(
                count_ident(&expr, "Membership.mem"),
                1,
                "the `∈ s` guard must survive as `Membership.mem`, not be discarded: {expr:?}"
            );
        }

        #[test]
        fn test_paren_bounded_forall_comparison_preserves_guard() {
            // `∀ (n > 0), P n`  ≡  `∀ n, n > 0 → P n`
            let expr = parse_expr("∀ (n > 0), P n").expect("parenthesized bounded ∀ should parse");
            match &expr {
                SurfaceExpr::Pi(_, binders, body) => {
                    assert_eq!(binders.len(), 1, "one bound name `n`");
                    assert!(
                        matches!(&**body, SurfaceExpr::Arrow(..)),
                        "guard `n > 0` must become the Arrow antecedent, got {body:?}"
                    );
                }
                other => panic!("expected Pi, got {other:?}"),
            }
            assert_eq!(
                count_ident(&expr, "GT.gt"),
                1,
                "the `> 0` guard must survive as `GT.gt`: {expr:?}"
            );
        }

        #[test]
        fn test_paren_bounded_exists_preserves_guard() {
            // `∃ (n > 0), P n`  ≡  `∃ n, n > 0 ∧ P n`
            let expr = parse_expr("∃ (n > 0), P n").expect("parenthesized bounded ∃ should parse");
            // Exists desugars to `Exists (fun n => And (GT.gt n 0) (P n))`.
            assert_eq!(
                count_ident(&expr, "GT.gt"),
                1,
                "the `> 0` guard must survive as `GT.gt` inside the ∃ body: {expr:?}"
            );
            assert_eq!(
                count_ident(&expr, "And"),
                1,
                "∃ (n > 0), P n must conjoin the guard with the body via `And`: {expr:?}"
            );
        }

        #[test]
        fn test_paren_bounded_forall_multiple_binders_preserve_all_guards() {
            // `∀ (a > 0) (b > 1), a = b`  ≡  `∀ a b, a > 0 → b > 1 → a = b`
            let expr = parse_expr("∀ (a > 0) (b > 1), a = b")
                .expect("multiple parenthesized bounded ∀ binders should parse");
            assert_eq!(
                count_ident(&expr, "GT.gt"),
                2,
                "both guards `a > 0` and `b > 1` must survive: {expr:?}"
            );
        }

        /// Regression for the arrow-speculation guard leak: parsing the TYPE
        /// of a binder like `(hs : ¬(r ≥ Int.ofNat w))` routes the inner
        /// parenthesized relation through `arrow_expr`'s speculative
        /// binder-arrow attempt, which recognized `(r ≥ …)` as a bounded
        /// binder and stashed its guard; the backtrack restored the token
        /// position but not the stash, so the enclosing `∀` drained a phantom
        /// `r ≥ Int.ofNat w →` antecedent around its body. Found because the
        /// trust bridge's composed all-18 conjunction stopped kernel-checking
        /// (its Shl/LShr/AShr arms carry exactly this hypothesis shape).
        #[test]
        fn paren_relation_inside_binder_type_leaks_no_guard() {
            let expr = parse_expr(
                "∀ (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w)) (h0 : 0 ≤ Int.mul l ((2 : Int) ^ r.toNat)), True",
            )
            .expect("shl-shaped fragment parses");
            match &expr {
                SurfaceExpr::Pi(_, binders, body) => {
                    assert_eq!(binders.len(), 5, "w, l, r, hs, h0 — nothing more");
                    assert!(
                        matches!(body.as_ref(), SurfaceExpr::Ident(_, name) if name == "True"),
                        "body must be exactly `True` — a leaked guard wraps it in an Arrow: {body:?}"
                    );
                }
                other => panic!("expected Pi, got {other:?}"),
            }
        }

        /// The arrow form `(n > 0) → U` is a PLAIN arrow whose domain is the
        /// proposition `n > 0` (binder-predicate sugar exists only under
        /// quantifiers) — the speculative binder reading must be rejected, not
        /// half-taken as `Pi([n], U)` with the guard dropped or leaked.
        #[test]
        fn paren_relation_arrow_is_plain_arrow_not_binder() {
            let expr = parse_expr("(n > 0) → True").expect("prop-domain arrow parses");
            match &expr {
                SurfaceExpr::Arrow(_, domain, body) => {
                    assert!(
                        matches!(body.as_ref(), SurfaceExpr::Ident(_, name) if name == "True"),
                        "codomain is True: {body:?}"
                    );
                    let d = format!("{domain:?}");
                    assert!(
                        d.contains("GT.gt") || d.contains('>'),
                        "domain keeps the relation: {d}"
                    );
                }
                other => panic!("expected plain Arrow, got {other:?}"),
            }
        }

        #[test]
        fn test_plain_paren_binder_has_no_spurious_guard() {
            // A normal typed binder `(n : Nat)` must NOT gain any guard Arrow.
            let expr =
                parse_expr("∀ (n : Nat), P n").expect("plain parenthesized ∀ binder should parse");
            match &expr {
                SurfaceExpr::Pi(_, _, body) => assert!(
                    !matches!(&**body, SurfaceExpr::Arrow(..)),
                    "`∀ (n : Nat), P n` body must be `P n`, not a guarded Arrow: {body:?}"
                ),
                other => panic!("expected Pi, got {other:?}"),
            }
        }

        /// Workaround: MATP-BENCH Q3 with explicit `in` separators
        ///
        /// Without layout-sensitive parsing, implicit let chaining where the
        /// body starts with `(` requires explicit `in` separators.
        /// See #105 for tracking full implicit let support.
        #[test]
        fn test_matp_bench_q3_with_explicit_separators() {
            // Version with explicit `in` separators - this works
            let code = r#"theorem pentagonAngleH (x : Real) :
  let angleE := x in
  let angleF := x + 20 in
  let angleG := x + 5 in
  let angleH := x - 5 in
  let angleJ := x + 10 in
  (angleE + angleF + angleG + angleH + angleJ = 540) ->
  angleH = 97 := by sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "Q3 with explicit separators should parse: {result:?}"
            );
        }

        #[test]
        fn test_multi_name_binder_in_type() {
            // Multi-name binders with shared type annotation
            // Used in dependent type signatures like: (x y z : List α) -> Type u

            // Test simple multi-name binder as expr - Issue #1251 verified working
            let expr = parse_expr("(x y z : Nat) → Type");
            assert!(
                expr.is_ok(),
                "Multi-name binder (x y z : T) → U should parse: {expr:?}"
            );

            // Test inductive with multi-name binder (file 1616)
            let code = r"inductive Cover : (x y z : List α) -> Type u
  | done  : Cover [] [] []";
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "Inductive with multi-name binder should parse: {result:?}"
            );
        }

        /// FATE-X file 40: Bounded forall with membership in theorem body
        /// The theorem signature includes `∀ p ∈ minimalPrimes R, ...`
        #[test]
        fn test_fate_x_file_40_bounded_membership() {
            let code = r#"theorem free_of_rank_iff (R : Type) [CommRing R] [IsLocalRing R] [IsReduced R]
    (h : (minimalPrimes R).Finite) (r : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Free R M ∧ Module.rank R M = r ↔
    (Module.rank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M) = r ∧
    ∀ p ∈ minimalPrimes R,
    Module.rank (FractionRing (R ⧸ p)) ((FractionRing (R ⧸ p)) ⊗[R] M) = r) := by
  sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "FATE-X file 40 (bounded ∀ membership) should parse: {result:?}"
            );
        }

        /// FATE-X file 98: Bounded forall with comparison in theorem body
        /// The theorem signature includes `∀ n > 0, m.comap (f ^ n) ≠ m`
        #[test]
        fn test_fate_x_file_98_bounded_comparison() {
            let code = r#"theorem exists_maximal_ideal_not_in_finite_order {K A : Type} [Field K] [NumberField K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {f : A →ₐ[K] A} (hf : ∀ n > 0, f ^ n ≠ 1) :
    ∃ m : Ideal A, m.IsMaximal ∧ ∀ n > 0, m.comap (f ^ n) ≠ m := by
  sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "FATE-X file 98 (bounded ∀ comparison) should parse: {result:?}"
            );
        }

        /// Test bounded forall at expression level (from file 40 body)
        ///
        /// Brick 1 (audit P0-4): this expression contains the quotient operator
        /// `⧸`, an infix operator Clean does not yet have a rule for. It
        /// previously "parsed" only because `R ⧸ p` was silently fabricated into
        /// a hole-slot application `(R _ p)` — the expression was never truly
        /// parsed. The honest baseline is a LOUD unknown-operator error until
        /// `⧸` (HDiv/quotient) lands in Brick 3. The bounded-∀ binder machinery
        /// this test targeted is still covered by
        /// `test_bounded_forall_complex_comparison_expr` below (no `⧸`).
        #[test]
        fn test_bounded_forall_complex_membership_expr_rejects_unknown_quotient_op() {
            let err = parse_expr("∀ p ∈ minimalPrimes R, Module.rank (FractionRing (R ⧸ p)) M = r")
                .expect_err("unknown infix `⧸` must be rejected loudly, not fabricated");
            assert!(
                matches!(err, crate::ParseError::UnexpectedToken { ref message, .. }
                    if message.contains("unknown operator")),
                "expected an unknown-operator error, got {err:?}"
            );
        }

        /// Test bounded forall with complex body (from file 98)
        #[test]
        fn test_bounded_forall_complex_comparison_expr() {
            let expr = parse_expr("∀ n > 0, m.comap (f ^ n) ≠ m");
            assert!(
                expr.is_ok(),
                "Complex bounded ∀ comparison expression should parse: {expr:?}"
            );
        }

        /// FATE-X file 94: PNat (ℕ+) notation in theorem signature
        /// The theorem has `∃ (d : ℕ+) (a : ℕ), ...`
        #[test]
        fn test_fate_x_file_94_pnat_notation() {
            let code = r#"def zeroSet : Set ℕ := {n | ∀ x : I, (ϕ.comp (f ^ n)) (x : A) = 0}

theorem zeroSet_finite_or_contain_arithmetic_progression (hf : f.FormallyEtale) :
    (zeroSet f ϕ I).Finite ∨ ∃ (d : ℕ+) (a : ℕ), ∀ n : ℕ, a + d * n ∈ zeroSet f ϕ I := by
  sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "FATE-X file 94 (PNat notation) should parse: {result:?}"
            );
        }

        /// Test PNat at expression level
        #[test]
        fn test_pnat_in_exists_binder() {
            let expr = parse_expr("∃ (d : ℕ+), P d");
            assert!(expr.is_ok(), "PNat in exists binder should parse: {expr:?}");
        }

        /// FATE-X file 97: Bare binder with arrow type annotation
        /// The theorem has `∃ a : τ → k, ...` without parentheses
        #[test]
        fn test_fate_x_file_97_bare_binder_arrow_type() {
            let code = r#"theorem exists_point_not_in_zero_set {τ k : Type} [Finite τ] [Nonempty τ] [Field k] [CharZero k]
    {f : τ → k[X]} (hfd : ∀ i : τ, (f i).natDegree ≥ 2): ∃ a : τ → k,
    ∀ p : MvPolynomial τ k, p ≠ 0 →
    ∃ m : ℕ, (((MvPolynomial.aeval (fun i ↦ (f i).toMvPolynomial i)) ^ m) p).aeval a ≠ 0 := by
  sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "FATE-X file 97 (bare binder arrow type) should parse: {result:?}"
            );
        }

        /// Test bare binder with arrow type at expression level
        #[test]
        fn test_bare_binder_arrow_type_expr() {
            let expr = parse_expr("∃ a : τ → k, P a");
            assert!(
                expr.is_ok(),
                "Bare binder with arrow type should parse: {expr:?}"
            );
        }

        /// Test forall with arrow type in bare binder
        #[test]
        fn test_forall_bare_binder_arrow_type() {
            let expr = parse_expr("∀ f : Nat → Bool, f 0 = true");
            assert!(
                expr.is_ok(),
                "Forall with arrow type in bare binder should parse: {expr:?}"
            );
        }

        /// Test FATE-X file 46: LinearMap bracket notation →ₗ[R]
        #[test]
        fn test_fate_x_file_46_linear_map_bracket_notation() {
            let code = r#"theorem module_flat_iff (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
    ∀ P : Type, ∀ (_ : AddCommGroup P), ∀ (_ : Module R P), ∀ f : P →ₗ[R] M, Module.FinitePresentation R P →
      ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F), Module.Finite R F ∧ Module.Free R F ∧
      ∃ h : P →ₗ[R] F, ∃ g : F →ₗ[R] M, f = g.comp h := by
  sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "FATE-X file 46 (LinearMap bracket notation) should parse: {result:?}"
            );
        }

        /// Test LinearMap bracket notation at expression level
        #[test]
        fn test_linear_map_bracket_expr() {
            let expr = parse_expr("∀ f : P →ₗ[R] M, P");
            assert!(
                expr.is_ok(),
                "LinearMap bracket notation should parse: {expr:?}"
            );
        }

        /// Test AlgHom bracket notation →ₐ[R]
        #[test]
        fn test_alg_hom_bracket_notation() {
            let expr = parse_expr("f : A →ₐ[K] A");
            assert!(
                expr.is_ok(),
                "AlgHom bracket notation should parse: {expr:?}"
            );
        }

        /// Test AlgEquiv bracket notation ≃ₐ[R]
        #[test]
        fn test_alg_equiv_bracket_notation() {
            let expr = parse_expr("e : A ≃ₐ[R] B");
            assert!(
                expr.is_ok(),
                "AlgEquiv bracket notation should parse: {expr:?}"
            );
        }

        /// Test absolute value notation |expr|
        /// Mathlib uses |x| for absolute value, parsing as `abs x`
        #[test]
        fn test_absolute_value_notation() {
            let expr = parse_expr("|x|");
            assert!(expr.is_ok(), "Simple absolute value should parse: {expr:?}");
        }

        /// Test absolute value in arithmetic expression
        #[test]
        fn test_absolute_value_arithmetic() {
            let expr = parse_expr("|2 * x - 3|");
            assert!(
                expr.is_ok(),
                "Absolute value with arithmetic should parse: {expr:?}"
            );
        }

        /// Test absolute value in compound expression
        #[test]
        fn test_absolute_value_compound() {
            let expr = parse_expr("|x| + |y|");
            assert!(
                expr.is_ok(),
                "Multiple absolute values should parse: {expr:?}"
            );
        }

        /// MATP-BENCH Q7: Absolute value in function definition
        /// Tests `|2 * x - 3| + 1` which is the core syntax in Q7
        #[test]
        fn test_matp_bench_q7_absolute_value() {
            let code = r#"def f (x : ℝ) : ℝ := |2 * x - 3| + 1
theorem derivative_equality : deriv f 2 = deriv f 5 := by sorry"#;
            let result = parse_file(code);
            assert!(
                result.is_ok(),
                "MATP-BENCH Q7 (absolute value) should parse: {result:?}"
            );
        }

        /// MATP-BENCH full suite test: Q1-Q10
        /// Tests all 10 MATP-BENCH problems parse correctly
        #[test]
        fn test_matp_bench_full_suite() {
            use std::fs;
            use std::path::Path;

            let matp_dir = Path::new("../../tests/matp_bench");
            if !matp_dir.exists() {
                println!("MATP-BENCH test files not found at {matp_dir:?}");
                return;
            }

            let mut passed = 0;
            let mut failed = 0;
            let mut failures = Vec::new();

            for i in 1..=10 {
                let path = matp_dir.join(format!("Q{i}.lean"));
                if !path.exists() {
                    continue;
                }

                let content = match fs::read_to_string(&path) {
                    Ok(c) => c,
                    Err(e) => {
                        failed += 1;
                        failures.push((format!("Q{i}"), format!("IO error: {e}")));
                        continue;
                    }
                };

                match parse_file(&content) {
                    Ok(_) => {
                        println!("PASS: Q{i}");
                        passed += 1;
                    }
                    Err(e) => {
                        let err_msg = format!("{e:?}");
                        let short_err = err_msg.lines().next().unwrap_or(&err_msg);
                        println!("FAIL: Q{i} - {short_err}");
                        failed += 1;
                        failures.push((format!("Q{i}"), err_msg));
                    }
                }
            }

            println!();
            println!("========================================");
            println!("MATP-BENCH Parse Compatibility Report");
            println!("========================================");
            println!("Passed: {passed}");
            println!("Failed: {failed}");
            if passed + failed > 0 {
                println!(
                    "Rate: {:.0}% ({}/{})",
                    100.0 * passed as f64 / (passed + failed) as f64,
                    passed,
                    passed + failed
                );
            }
            println!("========================================");

            if !failures.is_empty() {
                println!();
                println!("Failures:");
                for (name, err) in &failures {
                    let short_err = err.lines().next().unwrap_or(err);
                    println!("  {name}: {short_err}");
                }
            }

            // Allow some failures for incomplete features, but track progress
            assert!(
                passed >= 9,
                "MATP-BENCH should parse at least 9/10 files, got {passed}/{} (failures: {:?})",
                passed + failed,
                failures.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>()
            );
        }
    }
}
