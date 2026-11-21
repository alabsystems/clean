// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How a kernel term appears inside a user-facing error message.
//!
//! One place decides this, so the answer cannot drift per call site.
//!
//! # Why this module exists
//!
//! Error messages across the elaborator were built with `format!("{expr:?}")`
//! — Rust's derived `Debug` — on `Expr`, `Name` and kernel error types, all of
//! which carry hand-written `Display` impls intended for exactly this purpose.
//! `Name`'s `Debug` is the clearest case: it renders
//!
//! ```text
//! Name { depth: 1, suffix: ["P"], lean4_hash: ec950bf51f77e6a0 }
//! ```
//!
//! to say `P`. Measured over the 497-entry 2026-08-25 source-elaboration
//! corpus (`reports/source-elab/srcelab-2026-08-25-g08b7b05d9.json`): **80 of
//! the 320 error entries contain a Debug-printed `Name`, 166 occurrences in
//! all, occupying 11,043 characters where `Display` would use about 719** — a
//! mean of **67 characters per name instead of 4**.
//!
//! That is not merely verbose. The report truncates each message at 400
//! characters, and **43 of those 80 entries hit the truncation** — so a
//! substantial share of the "the artifact cut the `got` side, we need a corpus
//! re-run to read it" problem is self-inflicted: the budget was spent on struct
//! punctuation before the message reached its own content.
//!
//! # What this does not do
//!
//! It does not pretty-print in the elaborator's richer style
//! (`tactic::display::format_expr`, which resolves notation and needs an
//! `Environment`). The kernel `Display` needs no context, so it is available at
//! every site including the ones deep in unification that hold no environment.
//! A site that HAS an environment and wants notation should use the tactic
//! formatter directly; this is the floor, not the ceiling.

mod budget;

use clean_kernel::{Expr, ExprKind, FVarId, Level, LocalContext};
use clean_parser::surface::{SurfaceExpr, SurfaceLit, SurfacePattern};

/// Render a term for an error message.
///
/// Use this instead of `format!("{expr:?}")` anywhere the result can reach a
/// user, a report, or the JSON-RPC surface.
///
/// Preflight bounds node occurrences, depth and leaf payload before rendering;
/// oversized terms get an explicit omission marker. Small terms retain the
/// existing Display and private-name spelling.
#[must_use]
pub(crate) fn term(expr: &Expr) -> String {
    // A private constant shows its user-facing name, as Lean 4.8.0's
    // messages do under the default `pp.privateNames false` (`decide`'s
    // "proposition `pd 1 = 3` is false", G21). The fold runs only when the
    // rendering spells a private name; the preflight also bounds that fold.
    if !budget::fits(expr) {
        return "<term omitted: rendering budget exceeded>".to_string();
    }
    let text = expr.to_string();
    if !text.contains(crate::private_names::PRIVATE_HEADER) {
        return text;
    }
    crate::private_names::user_facing_expr(expr).to_string()
}

/// For a value whose `Debug` genuinely IS its best user-facing rendering.
///
/// Some things in an error message are `std` containers and index types — a
/// `Range<usize>`, a `Vec<usize>` of slot positions, an internal enum with no
/// `Display` — where `{:?}` is not a shortcut but the correct answer, and
/// inventing a `Display` for them would be ceremony.
///
/// Using this instead of a bare `{:?}` costs nothing and buys two things. The
/// error-render ratchet can reach **zero**, so any NEW `{:?}` in an error path
/// is a failure rather than a small increment nobody notices. And every
/// remaining Debug rendering becomes greppable as a decision somebody made,
/// rather than a default nobody looked at.
///
/// It is itself ratcheted (`OPAQUE_RENDER_SITE_RATCHET`), shrink-only, so the
/// escape hatch cannot quietly become the norm. Do not reach for it when the
/// value is a kernel term, a level, a name, an identifier or user syntax —
/// those all have real renderers above and below.
#[must_use]
pub(crate) fn opaque<T: std::fmt::Debug + ?Sized>(value: &T) -> String {
    format!("{value:?}")
}

/// Render a universe level for an error message.
///
/// `Level` carries a hand-written `Display` like `Expr` and `Name` do; the
/// sort-mismatch messages were Debug-printing it as `Succ(Param(Name { .. }))`.
#[must_use]
pub(crate) fn level(l: &Level) -> String {
    l.to_string()
}

/// Render a list of universe levels, as they are written in source: `{u, v}`.
#[must_use]
pub(crate) fn levels(ls: &[Level]) -> String {
    format!(
        "{{{}}}",
        ls.iter().map(level).collect::<Vec<_>>().join(", ")
    )
}

/// Name the SHAPE of a term, for a message that is about shapes.
///
/// The unifier reported a shape mismatch as
/// `std::mem::discriminant(left.kind())`, whose `Debug` is `Discriminant(6)` —
/// an opaque index into a private enum, printed as the entire explanation. It
/// destroys the term rather than merely spelling it badly, and CLAUDE.md
/// records it costing a real diagnosis: the `BEx.elim` face read
/// `TypeMismatch … "Discriminant(0) vs Discriminant(1)"`, which named nothing.
#[must_use]
pub(crate) fn kind_name(e: &Expr) -> &'static str {
    match e.kind() {
        ExprKind::BVar(_) => "a bound variable",
        ExprKind::FVar(_) => "a free variable",
        ExprKind::Sort(_) => "a sort",
        ExprKind::Const(..) => "a constant",
        ExprKind::App(..) => "an application",
        ExprKind::Lam(..) => "a lambda",
        ExprKind::Pi(..) => "a function type",
        ExprKind::Let(..) => "a let",
        ExprKind::Lit(_) => "a literal",
        ExprKind::Proj(..) => "a projection",
        ExprKind::MData(..) => "an annotated term",
        ExprKind::SProp => "SProp",
        ExprKind::Squash(_) => "a squash",
        // The cubical and ZFC families are grouped rather than enumerated: a
        // shape-mismatch message needs to say WHICH SIDE is which kind, and
        // "a cubical term" already does that. Splitting them into eleven arms
        // would add words without adding discrimination.
        ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::CubicalPath { .. }
        | ExprKind::CubicalPathLam { .. }
        | ExprKind::CubicalPathApp { .. }
        | ExprKind::CubicalHComp { .. }
        | ExprKind::CubicalTransp { .. }
        | ExprKind::CubicalCoe { .. } => "a cubical term",
        ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
            "a ZFC set term"
        }
    }
}

/// Render a free variable, decoding a metavariable if that is what it is.
///
/// # Why this exists
///
/// Metavariables ARE free variables here: `MetaState::to_fvar` sets bit 63
/// (`unify::meta_state::META_FVAR_TAG`). Every renderer in the tree treats an
/// `FVar` as an opaque local and prints its integer, so a diagnostic whose real
/// content is "`?m2` was never solved" comes out as
/// `FVar(FVarId(9223372036854775810))`.
///
/// Decoding needs **no context** — `MetaState::from_fvar` is a pure function of
/// the id. Measured over the 2026-08-25 source-elab corpus: 43 messages carry
/// at least one meta-tagged id, spanning 22 distinct `MetaId`s. Naming a plain
/// hypothesis is the other half and does need a `LocalContext`; pass one when
/// the caller holds it.
///
/// Caution for a future reader: `do_notation_desugar` mints fvars from a
/// counter that also starts at `1 << 63`, so a `?mN` printed here could in
/// principle be a do-desugar local. That path has no non-test caller today.
#[must_use]
pub(crate) fn fvar(id: FVarId, ctx: Option<&LocalContext>) -> String {
    if let Some(meta) = crate::unify::MetaState::from_fvar(id) {
        return format!("?m{}", meta.0);
    }
    if let Some(decl) = ctx.and_then(|c| c.get(id)) {
        return decl.name.to_string();
    }
    format!("fvar#{}", id.as_u64())
}

// ---------------------------------------------------------------------------
// Surface syntax
// ---------------------------------------------------------------------------
//
// A refusal about syntax the USER WROTE should quote the user, not dump the
// parser's AST. `SurfacePattern` and `SurfaceLit` are small enough to print as
// real syntax, so these do; `SurfaceExpr` has 32 variants and gets a shape NAME
// instead, which is honest about being a summary and still strictly better than
// `App(Span { start: 42, end: 51 }, Ident(Span { .. }, "Foo"), [ .. ])`.
//
// Measured scope note, so nobody over-values this: the 2026-08-25 source-elab
// corpus contains ZERO surface-AST dumps. Every `BinderData`/`Span` string in
// it comes from the kernel `Expr` path fixed separately. These sites are
// unsupported-syntax refusals for `do`-notation, `if let` and q-patterns, which
// the five pinned Mathlib files never reach. The audience here is the person
// writing Lean through Clean interactively, not the corpus.

/// Print a literal as the user wrote it.
#[must_use]
pub(crate) fn lit(l: &SurfaceLit) -> String {
    match l {
        SurfaceLit::Nat(n) => n.to_string(),
        SurfaceLit::BigNat(n) => n.to_string(),
        SurfaceLit::Float(text) => text.clone(),
        // Quoting is load-bearing: an unquoted `a` / `3` would be
        // indistinguishable from the identifier `a` and the numeral `3`, which
        // is precisely the confusion these messages exist to resolve.
        SurfaceLit::Char(c) => format!("'{c}'"),
        SurfaceLit::String(text) => format!("{text:?}"),
    }
}

/// Print a pattern as the user wrote it.
///
/// Nested constructor applications and alternations are parenthesised so the
/// rendering re-parses to the same shape; the top level is not wrapped.
#[must_use]
pub(crate) fn pattern(p: &SurfacePattern) -> String {
    pattern_prec(p, false)
}

fn pattern_prec(p: &SurfacePattern, nested: bool) -> String {
    let wrap = |s: String| if nested { format!("({s})") } else { s };
    match p {
        SurfacePattern::Var(name) => surface_name(name),
        SurfacePattern::Wildcard => "_".to_string(),
        SurfacePattern::Lit(l) => lit(l),
        SurfacePattern::Ctor(name, args) if args.is_empty() => surface_name(name),
        SurfacePattern::Ctor(name, args) => wrap(format!(
            "{} {}",
            surface_name(name),
            args.iter()
                .map(|a| pattern_prec(a, true))
                .collect::<Vec<_>>()
                .join(" ")
        )),
        SurfacePattern::NumeralAdd(inner, k) => {
            wrap(format!("{} + {k}", pattern_prec(inner, true)))
        }
        SurfacePattern::As(name, inner) => wrap(format!(
            "{}@{}",
            surface_name(name),
            pattern_prec(inner, true)
        )),
        SurfacePattern::Or(a, b) => wrap(format!(
            "{} | {}",
            pattern_prec(a, true),
            pattern_prec(b, true)
        )),
        // The inner term is a `SurfaceExpr`; naming its shape beats dumping it.
        SurfacePattern::Inaccessible(e) => format!(".({})", shape(e)),
        SurfacePattern::QPattern(e) => format!("q({})", shape(e)),
        SurfacePattern::Ellipsis => "..".to_string(),
        SurfacePattern::StructInst {
            fields,
            ellipsis,
            ty,
        } => {
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(name, pat)| {
                    format!("{} := {}", surface_name(name), pattern_prec(pat, false))
                })
                .collect();
            if *ellipsis {
                parts.push("..".to_string());
            }
            let ascription = ty
                .as_ref()
                .map(|ty| format!(" : {}", shape(ty)))
                .unwrap_or_default();
            format!("{{ {}{ascription} }}", parts.join(", "))
        }
    }
}

/// Diagnostic spelling only; unspellable generated identities are labelled.
pub(crate) fn surface_name(name: &clean_parser::SurfaceName) -> String {
    name.source_spelling()
        .unwrap_or_else(|| format!("<internal name {name}>"))
}

/// Name the CONSTRUCT a surface expression is, with its source span.
///
/// Deliberately a summary rather than a re-print: `SurfaceExpr` has 32 variants,
/// and a half-correct pretty-printer that silently mis-renders a user's term is
/// worse than an honest label. What a refusal needs is WHICH construct is
/// unsupported and WHERE it is, and that is what this gives. Identifiers and
/// literals are the exception — for those the name IS the useful answer, so they
/// are quoted exactly.
#[must_use]
pub(crate) fn shape(e: &SurfaceExpr) -> String {
    let name = match e {
        SurfaceExpr::Ident(_, n) => return format!("`{}`", surface_name(n)),
        SurfaceExpr::Lit(_, l) => return lit(l),
        SurfaceExpr::Hole(_) => return "`_`".to_string(),
        SurfaceExpr::SyntheticSorry(_) => "a synthetic `sorry`",
        SurfaceExpr::Universe(..) => "a universe",
        SurfaceExpr::App(..) => "an application",
        SurfaceExpr::Lambda(..) => "a `fun` lambda",
        SurfaceExpr::PatternMatchLambda(..) => "a pattern-matching lambda",
        SurfaceExpr::Pi(..) => "a binder type",
        SurfaceExpr::Arrow(..) => "an arrow type",
        SurfaceExpr::Let(..) => "a `let`",
        SurfaceExpr::Have(..) => "a `have`",
        SurfaceExpr::LetRec(..) => "a `let rec`",
        SurfaceExpr::LetPattern(..) => "a pattern `let`",
        SurfaceExpr::Paren(..) => "a parenthesised term",
        SurfaceExpr::NamedHole(..) => "a named hole",
        SurfaceExpr::Ascription(..) => "a type ascription",
        SurfaceExpr::Borrowed(..) => "a borrowed type annotation",
        SurfaceExpr::OutParam(..) => "an `outParam`",
        SurfaceExpr::SemiOutParam(..) => "a `semiOutParam`",
        SurfaceExpr::If(..) => "an `if`",
        SurfaceExpr::IfLet(..) => "an `if let`",
        SurfaceExpr::IfDecidable(..) => "a decidable `if`",
        SurfaceExpr::Match(..) => "a `match`",
        SurfaceExpr::Proj(..) => "a projection",
        SurfaceExpr::UniverseInst(..) => "a universe instantiation",
        SurfaceExpr::NamedArg(..) => "a named argument",
        SurfaceExpr::SyntaxQuote(..) => "a syntax quotation",
        SurfaceExpr::QQuotation { .. } => "a `q(..)` quotation",
        SurfaceExpr::QAntiquot { .. } => "an antiquotation",
        SurfaceExpr::Explicit(..) => "an `@`-explicit application",
        SurfaceExpr::StructLit { .. } => "a structure literal",
        SurfaceExpr::ByTactic(..) => "a `by` block",
        SurfaceExpr::CalcBlock(..) => "a `calc` block",
        SurfaceExpr::Do(..) => "a `do` block",
        SurfaceExpr::LiftMethod(..) => "a lifted method call",
        SurfaceExpr::InterpolatedStr { .. } => "an interpolated string",
        SurfaceExpr::OpenIn { .. } => "an `open .. in`",
        // NO wildcard, deliberately. The first draft had one, reasoning that a
        // build break in an error path is worse than a vague label — and the
        // compiler answered: `unreachable pattern`, this match is already
        // exhaustive. It should STAY exhaustive. New surface syntax then fails
        // to compile here until someone names it, which is exactly the right
        // moment to decide how a refusal about it should read.
    };
    let span = e.span();
    format!("{name} (bytes {}..{})", span.start, span.end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;
    use clean_parser::surface::Span;
    use clean_parser::SurfaceName;

    /// The measured claim in this module's header, as an executable arm: a
    /// bare constant's `Debug` is an order of magnitude longer than its
    /// `Display`, and the `Display` is the readable one.
    #[test]
    fn test_term_is_far_shorter_than_debug_for_a_named_constant() {
        let e = Expr::const_(Name::from_string("P"), vec![]);
        let rendered = term(&e);
        let debug = format!("{e:?}");

        assert!(
            rendered.contains('P'),
            "the rendering must name the constant, got: {rendered}"
        );
        assert!(
            !rendered.contains("lean4_hash"),
            "the rendering must not leak Name's struct fields, got: {rendered}"
        );
        assert!(
            debug.len() > rendered.len() * 4,
            "the whole point is the size gap; Debug={} Display={}",
            debug.len(),
            rendered.len()
        );
    }

    // -----------------------------------------------------------------------
    // Surface syntax
    // -----------------------------------------------------------------------

    #[test]
    fn test_lit_prints_the_value_and_keeps_kinds_distinguishable() {
        assert_eq!(lit(&SurfaceLit::Nat(3)), "3");
        assert_eq!(lit(&SurfaceLit::Float("3.14".to_string())), "3.14");
        // Quoting is load-bearing: unquoted, `a` and `3` would be
        // indistinguishable from the identifier and the numeral — precisely
        // the confusion these messages exist to resolve.
        assert_eq!(lit(&SurfaceLit::Char('a')), "'a'");
        assert_eq!(lit(&SurfaceLit::String("3".to_string())), "\"3\"");
    }

    #[test]
    fn test_pattern_prints_what_the_user_wrote() {
        assert_eq!(
            pattern(&SurfacePattern::Var(SurfaceName::generated_path("x"))),
            "x"
        );
        assert_eq!(pattern(&SurfacePattern::Wildcard), "_");
        assert_eq!(pattern(&SurfacePattern::Lit(SurfaceLit::Nat(0))), "0");
        assert_eq!(pattern(&SurfacePattern::Ellipsis), "..");
        assert_eq!(
            pattern(&SurfacePattern::Ctor(
                SurfaceName::generated_path("Nat.zero"),
                vec![]
            )),
            "Nat.zero",
            "a nullary constructor takes no trailing space"
        );
    }

    /// Nesting is parenthesised so the rendering re-parses to the same shape,
    /// and the TOP level is not — `C a b`, never `(C a b)`.
    #[test]
    fn test_pattern_parenthesises_nesting_but_not_the_top_level() {
        let inner = SurfacePattern::Ctor(
            SurfaceName::generated_path("Nat.succ"),
            vec![SurfacePattern::Var(SurfaceName::generated_path("n"))],
        );
        assert_eq!(pattern(&inner), "Nat.succ n");

        let outer = SurfacePattern::Ctor(
            SurfaceName::generated_path("Prod.mk"),
            vec![inner, SurfacePattern::Wildcard],
        );
        assert_eq!(pattern(&outer), "Prod.mk (Nat.succ n) _");
    }

    #[test]
    fn test_pattern_renders_the_sugar_forms() {
        let np = SurfacePattern::NumeralAdd(
            Box::new(SurfacePattern::Var(SurfaceName::generated_path("n"))),
            1,
        );
        assert_eq!(pattern(&np), "n + 1");

        let asp = SurfacePattern::As(
            SurfaceName::generated_path("h"),
            Box::new(SurfacePattern::Wildcard),
        );
        assert_eq!(pattern(&asp), "h@_");

        let orp = SurfacePattern::Or(
            Box::new(SurfacePattern::Var(SurfaceName::generated_path("a"))),
            Box::new(SurfacePattern::Var(SurfaceName::generated_path("b"))),
        );
        assert_eq!(pattern(&orp), "a | b");
    }

    /// A pattern rendering must never leak the parser's struct fields — that is
    /// the whole defect this replaces.
    #[test]
    fn test_pattern_never_leaks_the_ast() {
        let p = SurfacePattern::Inaccessible(Box::new(SurfaceExpr::Ident(
            Span::new(4, 7),
            SurfaceName::generated_path("foo"),
        )));
        let rendered = pattern(&p);
        assert!(!rendered.contains("Span {"), "got: {rendered}");
        assert!(!rendered.contains("Ident("), "got: {rendered}");
        assert!(rendered.contains("foo"), "got: {rendered}");
    }

    /// `shape` names the construct and locates it.
    #[test]
    fn test_shape_names_the_construct_and_its_span() {
        let e = SurfaceExpr::Lambda(
            Span::new(10, 20),
            vec![],
            Box::new(SurfaceExpr::Hole(Span::new(18, 19))),
        );
        let rendered = shape(&e);
        assert!(rendered.contains("lambda"), "got: {rendered}");
        assert!(
            rendered.contains("10..20"),
            "the span locates it: {rendered}"
        );
        assert!(!rendered.contains("Span {"), "got: {rendered}");
    }

    /// An identifier and a literal are worth quoting exactly, not summarising —
    /// the SHAPE of `foo` is not useful, the name is.
    #[test]
    fn test_shape_quotes_identifiers_and_literals_instead_of_summarising() {
        assert_eq!(
            shape(&SurfaceExpr::Ident(
                Span::new(0, 3),
                SurfaceName::generated_path("foo")
            )),
            "`foo`"
        );
        assert_eq!(
            shape(&SurfaceExpr::Lit(Span::new(0, 1), SurfaceLit::Nat(7))),
            "7"
        );
    }

    // -----------------------------------------------------------------------
    // Shapes and free variables
    // -----------------------------------------------------------------------

    #[test]
    fn test_kind_name_names_the_shape_in_user_vocabulary() {
        assert_eq!(kind_name(&Expr::prop()), "a sort");
        assert_eq!(
            kind_name(&Expr::const_(Name::from_string("Nat"), vec![])),
            "a constant"
        );
        let app = Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            Expr::const_(Name::from_string("x"), vec![]),
        );
        assert_eq!(kind_name(&app), "an application");
        assert_eq!(
            kind_name(&Expr::arrow(Expr::prop(), Expr::prop())),
            "a function type"
        );
    }

    /// A metavariable IS an fvar with bit 63 set. Decoding it needs no context,
    /// and 43 corpus messages carried one as a 19-digit integer.
    #[test]
    fn test_fvar_decodes_a_metavariable_without_any_context() {
        let id = crate::unify::MetaState::to_fvar(crate::unify::MetaId(2));
        assert_eq!(
            id.as_u64(),
            9_223_372_036_854_775_810,
            "this is the exact integer the corpus prints; if the tag moves, the \
             message this test defends changes with it"
        );
        assert_eq!(fvar(id, None), "?m2");
    }

    /// A plain local with no context available still renders as something
    /// short and honest, never a struct dump.
    #[test]
    fn test_fvar_without_a_context_falls_back_to_a_short_id() {
        let rendered = fvar(FVarId::new(7), None);
        assert_eq!(rendered, "fvar#7");
        assert!(!rendered.contains("FVarId("), "got: {rendered}");
    }

    /// Given a context, a plain local renders as its HYPOTHESIS NAME — the
    /// half of this that a reader can actually act on.
    #[test]
    fn test_fvar_with_a_context_renders_the_hypothesis_name() {
        // `push` mints the id itself, so take the one it returns rather than
        // asserting which number it will choose.
        let mut ctx = LocalContext::new();
        let id = ctx.push(
            Name::from_string("hab"),
            Expr::prop(),
            clean_kernel::BinderInfo::Default,
        );
        assert_eq!(fvar(id, Some(&ctx)), "hab");
    }

    /// The meta tag wins over a context lookup: a tagged id is never a
    /// hypothesis, and reporting one as a name would be a lie.
    #[test]
    fn test_fvar_prefers_the_meta_decode_over_a_context_hit() {
        let id = crate::unify::MetaState::to_fvar(crate::unify::MetaId(5));
        let ctx = LocalContext::new();
        assert_eq!(fvar(id, Some(&ctx)), "?m5");
    }
}
