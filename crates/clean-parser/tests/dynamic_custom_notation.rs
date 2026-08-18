// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dynamic custom-notation: a fixed-arity operator declared earlier in a file
//! (`infixl`/`infixr`/`prefix`/`postfix`) must be recognized by the surface
//! parser when used in a later expression, and lowered to the correct
//! application AST (`op a b => <expansion> a b`).
//!
//! Before this was fixed, the user-declared symbol was never consulted: the
//! unknown operator was lexed and dropped, so `def foo := a ** b` collapsed into
//! the parser's error-recovery `RawDecl` and the whole `def` was lost. These
//! tests pin the corrected behavior and guard against regressions in the
//! highest-blast-radius area (operator/expression parsing).

use clean_parser::{parse_file, Projection, SurfaceDecl, SurfaceExpr};

/// Return the value term of the `def <name>` in `decls`, failing loudly if the
/// declaration is missing or did not parse as a real `Def` (e.g. fell into
/// error-recovery as a `RawDecl`).
fn def_value<'a>(decls: &'a [SurfaceDecl], name: &str) -> &'a SurfaceExpr {
    for d in decls {
        match d {
            SurfaceDecl::Def { name: n, val, .. } if n == name => return val,
            SurfaceDecl::RawDecl { content, .. } if content.contains(name) => {
                panic!("`def {name}` fell into error recovery as RawDecl: {content:?}");
            }
            _ => {}
        }
    }
    panic!("no `def {name}` found in {decls:#?}");
}

/// Extract `(head_ident, args)` from `App(Ident(head), args)`.
fn as_app_of<'a>(expr: &'a SurfaceExpr, head: &str) -> &'a [clean_parser::SurfaceArg] {
    match expr {
        SurfaceExpr::App(_, f, args) => {
            match f.as_ref() {
                SurfaceExpr::Ident(_, name) => assert_eq!(
                    name, head,
                    "application head mismatch: expected {head:?}, got {name:?}"
                ),
                other => panic!("expected Ident head {head:?}, got {other:?}"),
            }
            args
        }
        other => panic!("expected App with head {head:?}, got {other:?}"),
    }
}

fn as_ident(expr: &SurfaceExpr) -> &str {
    match expr {
        SurfaceExpr::Ident(_, name) => name,
        other => panic!("expected Ident, got {other:?}"),
    }
}

#[test]
fn test_infixl_custom_operator_lowers_to_application() {
    // The headline case from the bug report.
    let code = "infixl:65 \" ** \" => mul\ndef foo := a ** b";
    let decls = parse_file(code).expect("file with custom infixl should parse");

    let val = def_value(&decls, "foo");
    let args = as_app_of(val, "mul");
    assert_eq!(args.len(), 2, "mul applied to exactly two operands");
    assert_eq!(as_ident(&args[0].expr), "a");
    assert_eq!(as_ident(&args[1].expr), "b");
}

#[test]
fn test_infixl_left_associative_nesting() {
    // `a ** b ** c` left-associates: `mul (mul a b) c`.
    let code = "infixl:65 \" ** \" => mul\ndef foo := a ** b ** c";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let outer = as_app_of(val, "mul");
    assert_eq!(outer.len(), 2);
    // Outer right operand is `c`; outer left operand is `mul a b`.
    assert_eq!(as_ident(&outer[1].expr), "c");
    let inner = as_app_of(&outer[0].expr, "mul");
    assert_eq!(as_ident(&inner[0].expr), "a");
    assert_eq!(as_ident(&inner[1].expr), "b");
}

#[test]
fn test_infixr_right_associative_nesting() {
    // `a ~> b ~> c` right-associates: `f a (f b c)`.
    let code = "infixr:65 \" ~> \" => f\ndef foo := a ~> b ~> c";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let outer = as_app_of(val, "f");
    assert_eq!(outer.len(), 2);
    // Outer left operand is `a`; outer right operand is `f b c`.
    assert_eq!(as_ident(&outer[0].expr), "a");
    let inner = as_app_of(&outer[1].expr, "f");
    assert_eq!(as_ident(&inner[0].expr), "b");
    assert_eq!(as_ident(&inner[1].expr), "c");
}

#[test]
fn test_prefix_custom_operator() {
    // `prefix:100 "‼" => bang` then `‼ x` => `bang x`.
    let code = "prefix:100 \"‼\" => bang\ndef foo := ‼ x";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let args = as_app_of(val, "bang");
    assert_eq!(args.len(), 1);
    assert_eq!(as_ident(&args[0].expr), "x");
}

#[test]
fn test_postfix_custom_operator() {
    // `postfix:max "⁇" => query` then `x ⁇` => `query x`.
    let code = "postfix:max \"⁇\" => query\ndef foo := x ⁇";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let args = as_app_of(val, "query");
    assert_eq!(args.len(), 1);
    assert_eq!(as_ident(&args[0].expr), "x");
}

#[test]
fn test_custom_operator_binds_looser_than_application() {
    // Operands are full applications: `f a ** g b` => `mul (f a) (g b)`.
    let code = "infixl:65 \" ** \" => mul\ndef foo := f a ** g b";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let outer = as_app_of(val, "mul");
    assert_eq!(outer.len(), 2);
    let lhs = as_app_of(&outer[0].expr, "f");
    assert_eq!(as_ident(&lhs[0].expr), "a");
    let rhs = as_app_of(&outer[1].expr, "g");
    assert_eq!(as_ident(&rhs[0].expr), "b");
}

#[test]
fn test_multitoken_symbol_does_not_match_single_token() {
    // `**` is two `Star` tokens; a genuine single `*` (HMul) must NOT be
    // misread as the custom operator. With `**` registered, `a * b` still
    // lowers to the builtin `HMul.hMul`.
    let code = "infixl:65 \" ** \" => mul\ndef foo := a * b";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let args = as_app_of(val, "HMul.hMul");
    assert_eq!(args.len(), 2);
    assert_eq!(as_ident(&args[0].expr), "a");
    assert_eq!(as_ident(&args[1].expr), "b");
}

#[test]
fn test_redeclaring_builtin_plus_does_not_shadow_builtin() {
    // A one-token symbol that re-lexes to a builtin operator (`+`) is not
    // registered as a custom operator, so the hand-written precedence chain
    // still owns it: `a + b` => `HAdd.hAdd a b`. This protects the builtin
    // operator parses from any blast radius.
    let code = "infixl:65 \" + \" => myadd\ndef foo := a + b";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let args = as_app_of(val, "HAdd.hAdd");
    assert_eq!(args.len(), 2);
    assert_eq!(as_ident(&args[0].expr), "a");
    assert_eq!(as_ident(&args[1].expr), "b");
}

#[test]
fn test_undeclared_operator_unaffected() {
    // Without any notation declaration, the parser behaves exactly as before:
    // `a ** b` is not a valid expression and the `def` falls into recovery.
    // (Pins that the registry is empty for files that declare nothing.)
    let code = "def foo := a ** b";
    let decls = parse_file(code).expect("parse should still succeed via recovery");
    // No real `Def { name: "foo", val: App(mul, ..) }` is produced.
    let has_real_def = decls.iter().any(|d| {
        matches!(
            d,
            SurfaceDecl::Def { name, val, .. }
                if name == "foo" && matches!(val.as_ref(), SurfaceExpr::App(..))
                    && matches!(
                        val.as_ref(),
                        SurfaceExpr::App(_, f, _)
                            if matches!(f.as_ref(), SurfaceExpr::Ident(_, n) if n == "mul")
                    )
        )
    });
    assert!(
        !has_real_def,
        "without a notation decl, `a ** b` must not lower to a custom operator"
    );
}

#[test]
fn test_custom_operator_in_theorem_body() {
    // The operator is consulted anywhere `expr` is used, including theorem
    // proof terms — `a ** b` inside a theorem lowers correctly.
    let code = "infixl:65 \" ** \" => mul\ntheorem t : P := a ** b";
    let decls = parse_file(code).expect("parse");

    let proof = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Theorem { name, proof, .. } if name == "t" => Some(proof),
            _ => None,
        })
        .expect("theorem `t` should parse as a real Theorem");
    let args = as_app_of(proof, "mul");
    assert_eq!(args.len(), 2);
    assert_eq!(as_ident(&args[0].expr), "a");
    assert_eq!(as_ident(&args[1].expr), "b");
}

#[test]
fn test_custom_operator_does_not_leak_across_parse_calls() {
    // Single-shot `parse_file` starts with an empty registry. A custom operator
    // declared in one call must not affect a later, separate call.
    let _ = parse_file("infixl:65 \" ** \" => mul").expect("parse");
    let decls = parse_file("def foo := a ** b").expect("parse");
    let has_real_def = decls.iter().any(|d| {
        matches!(d, SurfaceDecl::Def { name, .. } if name == "foo")
            && matches!(def_value(&decls, "foo"), SurfaceExpr::App(..))
    });
    assert!(
        !has_real_def
            || !matches!(def_value(&decls, "foo"), SurfaceExpr::App(_, f, _)
            if matches!(f.as_ref(), SurfaceExpr::Ident(_, n) if n == "mul")),
        "custom operator from a prior parse_file must not leak into a new one"
    );
}

#[test]
fn test_projection_still_parses_with_custom_operator_registered() {
    // Guard: registering a custom operator must not disturb unrelated atom/app
    // parsing such as field projection.
    let code = "infixl:65 \" ** \" => mul\ndef foo := p.x";
    let decls = parse_file(code).expect("parse");
    let val = def_value(&decls, "foo");
    match val {
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            assert_eq!(as_ident(base), "p");
            assert_eq!(field, "x");
        }
        other => panic!("expected projection p.x, got {other:?}"),
    }
}

#[test]
fn test_two_custom_operators_same_precedence_chain_left() {
    // Two distinct custom operators declared at the SAME precedence both parse,
    // and a mixed chain `a ** b ++ c` left-associates across them:
    // `add (mul a b) c`. This is the well-defined case the minimal feature
    // supports today.
    let code = "infixl:65 \" ** \" => mul\ninfixl:65 \" ++ \" => add\ndef foo := a ** b ++ c";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let outer = as_app_of(val, "add");
    assert_eq!(outer.len(), 2);
    assert_eq!(as_ident(&outer[1].expr), "c");
    let inner = as_app_of(&outer[0].expr, "mul");
    assert_eq!(as_ident(&inner[0].expr), "a");
    assert_eq!(as_ident(&inner[1].expr), "b");
}

#[test]
fn test_two_custom_operators_mixed_precedence_group_correctly() {
    // B100 made declared custom precedence authoritative: `**` (70) binds
    // tighter than `++` (65), so `a ++ b ** c` is `add a (mul b c)`.
    let code = "infixl:70 \" ** \" => mul\ninfixl:65 \" ++ \" => add\ndef foo := a ++ b ** c";
    let decls = parse_file(code).expect("parse");

    let val = def_value(&decls, "foo");
    let outer = as_app_of(val, "add");
    assert_eq!(as_ident(&outer[0].expr), "a");
    let inner = as_app_of(&outer[1].expr, "mul");
    assert_eq!(as_ident(&inner[0].expr), "b");
    assert_eq!(as_ident(&inner[1].expr), "c");
}

#[test]
fn test_temporal_relation_precedences_parse_and_group() {
    // Trust's public temporal surface deliberately uses relation precedences:
    // `~>` at 50 and `⊨` at 45. The tighter leads-to relation must stay in the
    // RHS of satisfies, and a parenthesized level-50 proposition must remain a
    // real theorem declaration rather than degrading through error recovery.
    let code = r#"
infixl:50 " ~> " => LeadsTo
infixl:45 " ⊨ " => Satisfies
def grouped := m ⊨ f ~> g
def grouped_and := m ⊨ f ∧ h
def grouped_arrow := m ⊨ f → h
def grouped_prod_left := a × b ~> c
def grouped_prod_right := a ~> b × c
def grouped_sum := a ⊕ b ~> c
def grouped_parenthesized := (a × b) ~> c
def grouped_cmp_left := a = b ~> c
def grouped_forall := p ~> ∀ x : T, q
def grouped_binder_arrow_parenthesized := p ~> ((x : T) → q)
theorem unfolds : (f ~> g) = LeadsTo f g := proof
"#;
    let decls = parse_file(code).expect("temporal relation notation should parse");

    assert!(
        decls
            .iter()
            .all(|decl| !matches!(decl, SurfaceDecl::RawDecl { .. })),
        "low-precedence temporal notation must not enter error recovery: {decls:#?}",
    );

    let grouped = def_value(&decls, "grouped");
    let satisfies = as_app_of(grouped, "Satisfies");
    assert_eq!(as_ident(&satisfies[0].expr), "m");
    let leads_to = as_app_of(&satisfies[1].expr, "LeadsTo");
    assert_eq!(as_ident(&leads_to[0].expr), "f");
    assert_eq!(as_ident(&leads_to[1].expr), "g");

    let and_args = as_app_of(def_value(&decls, "grouped_and"), "And");
    let and_left = as_app_of(&and_args[0].expr, "Satisfies");
    assert_eq!(as_ident(&and_left[0].expr), "m");
    assert_eq!(as_ident(&and_left[1].expr), "f");
    assert_eq!(as_ident(&and_args[1].expr), "h");

    match def_value(&decls, "grouped_arrow") {
        SurfaceExpr::Arrow(_, domain, codomain) => {
            let domain = as_app_of(domain, "Satisfies");
            assert_eq!(as_ident(&domain[0].expr), "m");
            assert_eq!(as_ident(&domain[1].expr), "f");
            assert_eq!(as_ident(codomain), "h");
        }
        other => panic!("expected (m ⊨ f) → h, got {other:#?}"),
    }

    let prod_left = as_app_of(def_value(&decls, "grouped_prod_left"), "Prod");
    assert_eq!(as_ident(&prod_left[0].expr), "a");
    let prod_left_rhs = as_app_of(&prod_left[1].expr, "LeadsTo");
    assert_eq!(as_ident(&prod_left_rhs[0].expr), "b");
    assert_eq!(as_ident(&prod_left_rhs[1].expr), "c");

    let prod_right = as_app_of(def_value(&decls, "grouped_prod_right"), "Prod");
    let prod_right_lhs = as_app_of(&prod_right[0].expr, "LeadsTo");
    assert_eq!(as_ident(&prod_right_lhs[0].expr), "a");
    assert_eq!(as_ident(&prod_right_lhs[1].expr), "b");
    assert_eq!(as_ident(&prod_right[1].expr), "c");

    let sum = as_app_of(def_value(&decls, "grouped_sum"), "Sum");
    assert_eq!(as_ident(&sum[0].expr), "a");
    let sum_rhs = as_app_of(&sum[1].expr, "LeadsTo");
    assert_eq!(as_ident(&sum_rhs[0].expr), "b");
    assert_eq!(as_ident(&sum_rhs[1].expr), "c");

    let parenthesized = as_app_of(def_value(&decls, "grouped_parenthesized"), "LeadsTo");
    assert!(matches!(parenthesized[0].expr, SurfaceExpr::Paren(..)));
    assert_eq!(as_ident(&parenthesized[1].expr), "c");

    let cmp_left = as_app_of(def_value(&decls, "grouped_cmp_left"), "LeadsTo");
    let equality = as_app_of(&cmp_left[0].expr, "Eq");
    assert_eq!(as_ident(&equality[0].expr), "a");
    assert_eq!(as_ident(&equality[1].expr), "b");
    assert_eq!(as_ident(&cmp_left[1].expr), "c");

    let forall = as_app_of(def_value(&decls, "grouped_forall"), "LeadsTo");
    assert_eq!(as_ident(&forall[0].expr), "p");
    assert!(matches!(forall[1].expr, SurfaceExpr::Pi(..)));

    let binder_arrow = as_app_of(
        def_value(&decls, "grouped_binder_arrow_parenthesized"),
        "LeadsTo",
    );
    assert_eq!(as_ident(&binder_arrow[0].expr), "p");
    assert!(matches!(binder_arrow[1].expr, SurfaceExpr::Paren(..)));

    assert!(
        decls
            .iter()
            .any(|decl| matches!(decl, SurfaceDecl::Theorem { name, .. } if name == "unfolds")),
        "parenthesized level-50 relation theorem was lost: {decls:#?}",
    );
}

#[test]
fn test_level_50_custom_relation_cannot_feed_comparison_without_parentheses() {
    // Lean's non-associative comparison at the same precedence cannot take a
    // level-50 custom result as its left operand. The inverse order is covered
    // positively by `grouped_cmp_left` above.
    let code = "infixl:50 \" ~> \" => LeadsTo\ndef rejected := a ~> b = c";
    let decls = parse_file(code).expect("file parser should recover after the invalid declaration");
    assert!(
        !decls
            .iter()
            .any(|decl| matches!(decl, SurfaceDecl::Def { name, .. } if name == "rejected")),
        "`a ~> b = c` must not become an accepted definition: {decls:#?}",
    );
}

#[test]
fn test_low_custom_relation_rejects_unparenthesized_binder_arrow_rhs() {
    let code = "infixl:50 \" ~> \" => LeadsTo\ndef rejected := p ~> (x : T) → q";
    let decls = parse_file(code).expect("file parser should recover after the invalid declaration");
    assert!(
        !decls
            .iter()
            .any(|decl| matches!(decl, SurfaceDecl::Def { name, .. } if name == "rejected")),
        "unparenthesized binder-arrow RHS must fail closed: {decls:#?}",
    );
}

#[test]
fn test_low_custom_relation_rejects_dependent_product_tail() {
    for expression in [
        "(x : T) × q ~> r",
        "p × (x : T) × q ~> r",
        "p ~> (x : T) × q",
    ] {
        let code = format!("infixl:50 \" ~> \" => LeadsTo\ndef rejected := {expression}");
        let decls =
            parse_file(&code).expect("file parser should recover after the invalid declaration");
        assert!(
            !decls
                .iter()
                .any(|decl| matches!(decl, SurfaceDecl::Def { name, .. } if name == "rejected")),
            "dependent-product tail must fail closed for `{expression}`: {decls:#?}",
        );
    }
}

#[test]
fn test_low_precedence_postfix_fails_closed() {
    let code = "postfix:50 \" !! \" => Observe\ndef rejected := p !!";
    let decls = parse_file(code).expect("file parser should recover after the invalid declaration");
    assert!(
        !decls
            .iter()
            .any(|decl| matches!(decl, SurfaceDecl::Def { name, .. } if name == "rejected")),
        "unsupported low-precedence postfix must not leave a partial definition: {decls:#?}",
    );
}

// ===========================================================================
// Namespace-gated `scoped` notation (Phase 1 #4a): a `scoped infixl` is
// consulted only while its declaring namespace is active — inside the
// namespace, or after `open Ns` / `open scoped Ns` — and is INERT elsewhere
// (the use site falls into ordinary error recovery, never a silent lowering).
// ===========================================================================

/// Whether `decls` contains a real `def <name>` whose value lowered to a
/// two-argument application of `head` (the notation's expansion).
fn def_lowered_to(decls: &[SurfaceDecl], name: &str, head: &str) -> bool {
    fn walk<'a>(decls: &'a [SurfaceDecl], name: &str, out: &mut Option<&'a SurfaceExpr>) {
        for d in decls {
            match d {
                SurfaceDecl::Def { name: n, val, .. } if n == name => *out = Some(val),
                SurfaceDecl::Namespace { decls, .. } | SurfaceDecl::Section { decls, .. } => {
                    walk(decls, name, out);
                }
                _ => {}
            }
        }
    }
    let mut val = None;
    walk(decls, name, &mut val);
    match val {
        Some(SurfaceExpr::App(_, f, args)) => {
            matches!(f.as_ref(), SurfaceExpr::Ident(_, n) if n == head) && args.len() == 2
        }
        _ => false,
    }
}

#[test]
fn test_scoped_infixl_active_inside_declaring_namespace() {
    let code = "namespace Foo\nscoped infixl:65 \" ** \" => mul\ndef foo := a ** b\nend Foo";
    let decls = parse_file(code).expect("scoped infixl inside its namespace should parse");
    assert!(
        def_lowered_to(&decls, "foo", "mul"),
        "scoped infixl must be ACTIVE inside its declaring namespace: {decls:#?}"
    );
}

#[test]
fn test_scoped_infixl_inert_outside_namespace_without_open() {
    let code = "namespace Foo\nscoped infixl:65 \" ** \" => mul\nend Foo\ndef bar := a ** b";
    let decls = parse_file(code).expect("file parser should recover from the inert operator use");
    assert!(
        !def_lowered_to(&decls, "bar", "mul"),
        "scoped infixl must be INERT outside its namespace without an open: {decls:#?}"
    );
}

#[test]
fn test_scoped_infixl_active_after_open_scoped() {
    let code = "namespace Foo\nscoped infixl:65 \" ** \" => mul\nend Foo\nopen scoped Foo\ndef baz := a ** b";
    let decls = parse_file(code).expect("open scoped + scoped infixl use should parse");
    assert!(
        def_lowered_to(&decls, "baz", "mul"),
        "`open scoped Foo` must activate Foo's scoped infixl: {decls:#?}"
    );
}

#[test]
fn test_scoped_infixl_active_after_plain_open() {
    let code =
        "namespace Foo\nscoped infixl:65 \" ** \" => mul\nend Foo\nopen Foo\ndef qux := a ** b";
    let decls = parse_file(code).expect("plain open + scoped infixl use should parse");
    assert!(
        def_lowered_to(&decls, "qux", "mul"),
        "a simple `open Foo` must activate Foo's scoped infixl: {decls:#?}"
    );
}

#[test]
fn test_scoped_infixl_open_inside_section_does_not_leak() {
    let code = "namespace Foo\nscoped infixl:65 \" ** \" => mul\nend Foo\n\
                section\nopen scoped Foo\ndef inside := a ** b\nend\ndef outside := a ** b";
    let decls = parse_file(code).expect("file parser should recover from the post-section use");
    assert!(
        def_lowered_to(&decls, "inside", "mul"),
        "activation must be in force inside the section: {decls:#?}"
    );
    assert!(
        !def_lowered_to(&decls, "outside", "mul"),
        "`open scoped` inside a section must not leak past `end`: {decls:#?}"
    );
}

#[test]
fn test_unscoped_and_local_notation_remain_ungated() {
    // Plain and `local` notation keep their pre-existing file-wide parse
    // behavior — the namespace gate applies to `scoped` only.
    let code = "namespace Foo\ninfixl:65 \" ** \" => mul\nend Foo\ndef plainUse := a ** b";
    let decls = parse_file(code).expect("plain notation in a namespace should parse");
    assert!(
        def_lowered_to(&decls, "plainUse", "mul"),
        "plain notation must stay active file-wide: {decls:#?}"
    );

    let code = "local infixl:65 \" ** \" => mul\ndef localUse := a ** b";
    let decls = parse_file(code).expect("local notation should parse");
    assert!(
        def_lowered_to(&decls, "localUse", "mul"),
        "local notation must stay active in its file: {decls:#?}"
    );
}
