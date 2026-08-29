// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dynamic custom-notation support consulted *during* parsing.
//!
//! Lean 4 lets a file declare its own operators before using them:
//!
//! ```text
//! infixl:65 " ** " => mul
//! def foo := a ** b      -- parses as `mul a b`
//! ```
//!
//! `infixl` / `infixr` / `prefix` / `postfix` declare a *fixed-arity* operator
//! at a chosen precedence. When such a declaration is parsed inside a file, we
//! record it in the parser's notation registry ([`CustomOperator`]). Later
//! expression parsing consults that registry so the user-declared symbol is
//! recognized and lowered to the correct application AST
//! (`op a b  =>  <expansion> a b`).
//!
//! Precedence model (B100): a declared operator carries its Lean `:N` level and
//! is parsed against the BUILTIN operator levels (`+` = 65, `*` = 70, …) the
//! hand-written chain in `expr_operators.rs` encodes structurally. The chain
//! communicates its current operand level through `Parser::custom_min_prec`
//! (each builtin right-operand parse sets the Lean level of its slot), the
//! custom layers consume an operator only when `precedence >= custom_min_prec`,
//! and custom operands re-enter the builtin chain at the level dictated by the
//! operator via [`Parser::expr_at_custom_level`]. The arithmetic band models
//! levels 60 and tighter. Below it sit six infix bands, each owning the window
//! between two adjacent builtin connective levels and each entered from the
//! chain position that makes those builtins group correctly around it:
//!
//! | band | window | entered from | operands come from |
//! |---|---|---|---|
//! | [`Parser::very_low_custom_infix_expr`] | 0–10 | `expr` entry | `⟶` (10) |
//! | [`Parser::pipe_custom_infix_expr`] | 11–20 | `\|>` (10) | `<\|>`/`↔` (20) |
//! | [`Parser::iff_custom_infix_expr`] | 21–30 | `↔` (20) | `∨` (30) |
//! | [`Parser::or_custom_infix_expr`] | 31–35 | `∨` (30) | `∧` (35) |
//! | [`Parser::low_custom_infix_expr`] | 36–50 | `∧` (35) | `=` (50) |
//! | [`Parser::mid_custom_infix_expr`] | 51–59 | `=` (50) | `>>=` (55) |
//!
//! A band's operands are produced by the layer immediately BELOW it, so it owns
//! every level up to that layer's own; it is entered from the layer immediately
//! above it, so it owns nothing at or below that layer's level.
//!
//! `→` (25), `⊕` (30) and `×` (35) are reached BELOW all of them in the
//! hand-written call graph despite being looser than most, so a band rotates a
//! consumed operator through such a tail exactly when the tail's Lean level is
//! strictly lower than the operator's — see
//! [`apply_operator_across_looser_tails`]. Nothing in 0–59 fails closed for
//! being "unmodeled" any more.
//!
//! Scope: fixed-arity infix/prefix/postfix operators plus CLOSED multi-hole
//! `notation` patterns (leading + trailing literal, every hole delimited by
//! literals, e.g. `notation:max "⟪" a ", " b "⟫" => …`). Other `notation`
//! interleavings (binder notations, adjacent holes, keyword-leading patterns)
//! still parse into `SurfaceDecl::Notation` but register no parseable operator.

use super::Parser;
use crate::lexer::{Lexer, TokenKind};
use crate::surface::{
    DeclScope, NotationItem, NotationKind, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo,
    SurfaceExpr,
};
use crate::ParseError;

/// The ambient custom-operator operand level at full-expression positions
/// ([`Parser::expr`] entry). Lean's `term` parser is `term:0`, so every
/// declared precedence is admissible there; the individual bands below narrow
/// it to the window each one owns.
pub(super) const CUSTOM_PREC_FLOOR: u32 = 0;

/// Highest precedence owned by the low custom-infix band. Level 50 is the
/// comparison/relation boundary; the enclosing `and_expr` is level 35.
const CUSTOM_LOW_INFIX_CEILING: u32 = 50;

/// Lowest precedence owned by the low custom-infix band. Above it sit four
/// looser bands, one per builtin connective level, so nothing between 0 and 59
/// has to fail closed.
const CUSTOM_LOW_INFIX_FLOOR: u32 = 36;

/// Lowest precedence owned by the original arithmetic custom-operator band.
const CUSTOM_ARITHMETIC_FLOOR: u32 = 60;

/// Lean precedence of `→` (`infixr:25`, `Lean/Parser/Term.lean`). Also the
/// ambient custom-operator level inside an arrow codomain, which Lean parses as
/// `term:25`.
pub(super) const ARROW_LEVEL: u32 = 25;

/// Lean precedence of `⊕` (`Sum`, `infixr:30`).
const SUM_LEVEL: u32 = 30;

/// Lean precedence of `×` (`Prod`, `infixr:35`).
const PROD_LEVEL: u32 = 35;

/// Builtin binary forms whose implementation sits below `cmp_expr` in the
/// hand-written call graph even though their Lean precedences are lower than
/// it. A custom operator consumed by one of the bands above `cmp_expr` must be
/// rotated INTO such a tail whenever the tail binds LOOSER than the operator —
/// and left alone otherwise, which is what [`LooserBuiltin::level`] decides.
/// Parentheses produce `SurfaceExpr::Paren` and therefore intentionally stop
/// this re-association.
#[derive(Clone, Copy)]
enum LooserBuiltin {
    Arrow,
    Sum,
    Prod,
}

impl LooserBuiltin {
    /// The form's Lean precedence.
    fn level(self) -> u32 {
        match self {
            LooserBuiltin::Arrow => ARROW_LEVEL,
            LooserBuiltin::Sum => SUM_LEVEL,
            LooserBuiltin::Prod => PROD_LEVEL,
        }
    }
}

/// Split a parser-generated looser-binding builtin tail off `expr`, but ONLY
/// when it binds looser than `slot_level` — the Lean level of the OPERAND SLOT
/// the tail was parsed into, not the operator's own level. Lean declares
/// `infixl:n` as `term:n op term:(n+1)` and `infixr:n` as
/// `term:(n+1) op term:n`, and the pinned v4.30 oracle shows the two really do
/// differ at the boundary: `A ~L~ B → C` is `(A ~L~ B) → C` for an `infixl:25`
/// but `A ~R~ (B → C)` for an `infixr:25`.
fn split_looser_builtin(
    expr: SurfaceExpr,
    slot_level: u32,
) -> Result<(LooserBuiltin, SurfaceExpr, SurfaceExpr), SurfaceExpr> {
    match expr {
        SurfaceExpr::Arrow(span, left, right) => {
            if ARROW_LEVEL < slot_level {
                Ok((LooserBuiltin::Arrow, *left, *right))
            } else {
                Err(SurfaceExpr::Arrow(span, left, right))
            }
        }
        SurfaceExpr::App(span, head, args) => {
            let kind = match head.as_ref() {
                // `sum_expr`/`prod_expr` stamp their synthetic head with the
                // WHOLE notation span. An explicitly authored `Sum A B` or
                // `Prod A B` keeps the identifier's narrower token span and is
                // an application atom, not a looser infix tail.
                SurfaceExpr::Ident(head_span, name) if *head_span == span && name == "Sum" => {
                    Some(LooserBuiltin::Sum)
                }
                SurfaceExpr::Ident(head_span, name) if *head_span == span && name == "Prod" => {
                    Some(LooserBuiltin::Prod)
                }
                _ => None,
            };
            if let Some(kind) = kind.filter(|kind| kind.level() < slot_level) {
                if args.len() == 2 && args.iter().all(|arg| arg.name.is_none()) {
                    let mut args = args.into_iter();
                    let left = args.next().expect("binary builtin has a left operand").expr;
                    let right = args
                        .next()
                        .expect("binary builtin has a right operand")
                        .expr;
                    return Ok((kind, left, right));
                }
            }
            Err(SurfaceExpr::App(span, head, args))
        }
        other => Err(other),
    }
}

fn rebuild_looser_builtin(
    kind: LooserBuiltin,
    left: SurfaceExpr,
    right: SurfaceExpr,
) -> SurfaceExpr {
    let span = left.span().merge(right.span());
    match kind {
        LooserBuiltin::Arrow => SurfaceExpr::Arrow(span, Box::new(left), Box::new(right)),
        LooserBuiltin::Sum | LooserBuiltin::Prod => {
            let head = match kind {
                LooserBuiltin::Sum => "Sum",
                LooserBuiltin::Prod => "Prod",
                LooserBuiltin::Arrow => unreachable!(),
            };
            SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, head.to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            )
        }
    }
}

/// Generated dependent-product notation cannot be re-associated as an
/// ordinary binary tail without changing which expressions are in scope for
/// the binder. The parser-generated `Sigma`/`PSigma` application and its sole
/// lambda deliberately share the full notation span; explicitly authored
/// `Sigma (fun ..)` applications do not.
fn is_generated_dependent_product(expr: &SurfaceExpr) -> bool {
    let SurfaceExpr::App(span, head, args) = expr else {
        return false;
    };
    let SurfaceExpr::Ident(_, name) = head.as_ref() else {
        return false;
    };
    if name != "Sigma" && name != "PSigma" {
        return false;
    }
    matches!(
        args.as_slice(),
        [SurfaceArg {
            name: None,
            expr: SurfaceExpr::Lambda(lambda_span, _, _),
            ..
        }] if lambda_span == span
    )
}

/// Borrow the operands of a parser-generated lower-precedence binary form.
/// This mirrors `split_looser_builtin` without consuming the tree and is used
/// to validate the exact operands a custom relation would join. Gated by
/// `slot_level` for the same reason.
fn looser_builtin_children(
    expr: &SurfaceExpr,
    slot_level: u32,
) -> Option<(&SurfaceExpr, &SurfaceExpr)> {
    match expr {
        SurfaceExpr::Arrow(_, left, right) if ARROW_LEVEL < slot_level => Some((left, right)),
        SurfaceExpr::App(span, head, args) => {
            let SurfaceExpr::Ident(head_span, name) = head.as_ref() else {
                return None;
            };
            let level = match name.as_str() {
                _ if head_span != span => return None,
                "Sum" => SUM_LEVEL,
                "Prod" => PROD_LEVEL,
                _ => return None,
            };
            if level >= slot_level {
                return None;
            }
            let [left, right] = args.as_slice() else {
                return None;
            };
            if left.name.is_some() || right.name.is_some() {
                return None;
            }
            Some((&left.expr, &right.expr))
        }
        _ => None,
    }
}

fn rightmost_relation_operand(mut expr: &SurfaceExpr, slot_level: u32) -> &SurfaceExpr {
    while let Some((_, right)) = looser_builtin_children(expr, slot_level) {
        expr = right;
    }
    expr
}

fn leftmost_relation_operand(mut expr: &SurfaceExpr, slot_level: u32) -> &SurfaceExpr {
    while let Some((left, _)) = looser_builtin_children(expr, slot_level) {
        expr = left;
    }
    expr
}

/// Insert a tighter custom relation between the rightmost operands of any
/// unparenthesized lower-precedence builtin tails on its two sides. This is the
/// rotation the structurally non-monotone operator chain otherwise misses:
/// `A × B ~> C × D` becomes `A × ((B ~> C) × D)`. Parenthesized
/// subexpressions are opaque and retain their authored grouping.
///
/// `lhs_level` / `rhs_level` are the Lean levels of the operator's two operand
/// SLOTS (`infixl:n` ⇒ `n` / `n+1`, `infixr:n` ⇒ `n+1` / `n`, non-associative
/// `infix:n` ⇒ `n+1` / `n+1`). A tail binds looser than its slot only if its
/// level is strictly below it, so an `infixr:25` hom-arrow leaves an `→` (25)
/// exactly where the descent put it while an `infixl:25` — whose right slot is
/// `term:26` — rotates through it.
fn apply_operator_across_looser_tails(
    expansion: &SurfaceExpr,
    left: SurfaceExpr,
    right: SurfaceExpr,
    lhs_level: u32,
    rhs_level: u32,
) -> SurfaceExpr {
    let left = match split_looser_builtin(left, lhs_level) {
        Ok((kind, outer, inner)) => {
            return rebuild_looser_builtin(
                kind,
                outer,
                apply_operator_across_looser_tails(expansion, inner, right, lhs_level, rhs_level),
            );
        }
        Err(left) => left,
    };
    match split_looser_builtin(right, rhs_level) {
        Ok((kind, inner, outer)) => rebuild_looser_builtin(
            kind,
            apply_operator_across_looser_tails(expansion, left, inner, lhs_level, rhs_level),
            outer,
        ),
        Err(right) => apply_operator(expansion, left.span(), &[left, right]),
    }
}

/// A user-declared fixed-arity operator registered while parsing a file.
///
/// Only `infixl` / `infixr` / `prefix` / `postfix` produce an entry; the
/// general `notation` form is excluded (see module docs).
#[derive(Debug, Clone)]
pub(super) struct CustomOperator {
    /// The lexed token-kind sequence of the operator symbol, e.g. `**` lexes to
    /// `[Star, Star]` and `<+>` to `[Ident("<+>")]`. Matched by value against
    /// the upcoming token stream during expression parsing.
    pub(super) symbol_tokens: Vec<TokenKind>,
    /// `infixl` / `infixr` / `prefix` / `postfix`.
    pub(super) kind: NotationKind,
    /// Declared precedence (the `:N` suffix, Lean scale: `+` = 65, `*` = 70);
    /// `None` defaults to 65. Compared against `Parser::custom_min_prec` — the
    /// Lean level of the operand slot being parsed — to decide consumption.
    pub(super) precedence: u32,
    /// The expansion head: the term to the right of `=>`. Applied positionally
    /// to the operands.
    pub(super) expansion: SurfaceExpr,
    /// For `scoped` notation: the FULL declaring namespace path. The operator
    /// is consulted only while that namespace is active — the current
    /// namespace (or an ancestor of it) or one activated by `open` /
    /// `open scoped`. `None` for plain and `local` notation (always active,
    /// preserving the pre-existing `local` behavior).
    pub(super) scope_ns: Option<String>,
}

/// One element of a registered closed mixfix `notation` pattern.
#[derive(Debug, Clone)]
pub(super) enum MixfixItem {
    /// A literal separator/delimiter, stored as its lexed token sequence and
    /// matched by value against the token stream.
    Literal(Vec<TokenKind>),
    /// An operand hole, parsed as a full expression (Lean's un-annotated
    /// `notation` holes parse at term level between the delimiting literals).
    Hole,
}

/// A user-declared CLOSED multi-hole `notation` registered while parsing a
/// file: the pattern starts AND ends with a literal and every hole is
/// delimited by literals on both sides (`"⟪" a ", " b "⟫"`). Open shapes
/// (leading/trailing hole) are handled by the fixed-arity mapping in
/// [`classify_notation_shape`] or stay parse-only.
#[derive(Debug, Clone)]
pub(super) struct CustomMixfix {
    /// The alternating literal/hole pattern. Invariant: first and last items
    /// are `Literal`, no two adjacent `Hole`s.
    pub(super) items: Vec<MixfixItem>,
    /// Declared precedence of the whole notation (`:N` / `:max`); `None`
    /// defaults to max — closed delimiter pairs act atom-like.
    pub(super) precedence: u32,
    /// `fun <holes> => <template>`: the expansion abstracted over the hole
    /// variables in pattern order, beta-reduced against the parsed operands by
    /// the shared application machinery.
    pub(super) expansion: SurfaceExpr,
    /// For `scoped` notation: the FULL declaring namespace path (see
    /// [`CustomOperator::scope_ns`]). `None` = always active.
    pub(super) scope_ns: Option<String>,
}

impl Parser {
    /// Register an `infixl`/`infixr`/`prefix`/`postfix` operator so later
    /// expressions in the same file can use it.
    ///
    /// `notation` (general mixfix) and patterns that are not a single symbol
    /// literal are ignored — they remain `SurfaceDecl::Notation` only.
    pub(super) fn register_custom_operator(
        &mut self,
        kind: NotationKind,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
        scope: DeclScope,
    ) {
        // `scoped` notation registers against its declaring namespace and is
        // consulted only while that namespace is active. At root there is no
        // namespace to register against — skip parse-time registration; the
        // elaborator rejects the declaration loudly (Lean: "scoped attributes
        // must be used inside namespaces"), so nothing is silently dropped.
        let scope_ns = match scope {
            DeclScope::Scoped => match self.notation_ns_stack.last() {
                Some(current) => Some(current.clone()),
                None => return,
            },
            DeclScope::Default | DeclScope::Local => None,
        };
        self.register_custom_operator_ns(kind, precedence, pattern, expansion, scope_ns);
    }

    /// Register a notation whose declaring namespace is already resolved.
    ///
    /// [`Parser::register_custom_operator`] derives that namespace from the
    /// cursor's own `namespace` stack, which is the right answer for a
    /// declaration in the file being parsed. A notation SEEDED from an
    /// imported module (`crate::notation_seed`) was declared in a different
    /// file, under a namespace stack that no longer exists at the cursor, so
    /// it supplies its own — and everything downstream of this point is
    /// identical for the two. Keeping one body means a seeded notation can
    /// never be more capable, or differently modelled, than a declared one.
    pub(super) fn register_custom_operator_ns(
        &mut self,
        kind: NotationKind,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
        scope_ns: Option<String>,
    ) {
        // `infixl`/`infixr`/`prefix`/`postfix` name no operands in their pattern
        // (the operands are implicit) and their expansion is a bare head applied
        // positionally. The general `notation` command instead NAMES its operands
        // in the pattern and references them in the expansion as a template. When
        // a `notation` pattern is a simple infix `a "sym" b`, prefix `"sym" a`, or
        // postfix `a "sym"` shape, register it by mapping to the corresponding
        // fixed-arity kind and abstracting the named operands into a lambda
        // `fun <vars> => <expansion>`, so the shared application machinery
        // (`apply_operator`) beta-reduces the template against the operands. Any
        // other `notation` interleaving (multi-literal mixfix, binder notations,
        // a bare symbol) is left parse-only — registers no parseable operator,
        // exactly as before. Associativity beyond left-assoc and precedence
        // disambiguation between two custom `notation`s are not modelled (the
        // matcher is left-to-right); those remain parse-only failures.
        let (effective_kind, effective_expansion) = if matches!(kind, NotationKind::Notation) {
            let Some((mapped, vars)) = classify_notation_shape(pattern) else {
                // Not a simple fixed-arity shape — try the closed multi-hole
                // mixfix form (`"⟪" a ", " b "⟫"`); anything else stays
                // parse-only.
                self.register_custom_mixfix(precedence, pattern, expansion, scope_ns);
                return;
            };
            let binders: Vec<SurfaceBinder> = vars
                .into_iter()
                .map(|v| SurfaceBinder::new(v, None, SurfaceBinderInfo::Explicit))
                .collect();
            let lam = SurfaceExpr::Lambda(expansion.span(), binders, Box::new(expansion.clone()));
            (mapped, lam)
        } else {
            (kind, expansion.clone())
        };

        // The symbol is the single literal in the pattern. `infixl`/`infixr`
        // patterns are just the operator literal (the operands are implicit);
        // `prefix`/`postfix` likewise carry exactly one literal.
        let mut literals = pattern.iter().filter_map(|item| match item {
            NotationItem::Literal(s) => Some(s),
            NotationItem::Variable(_) => None,
        });
        let Some(symbol) = literals.next() else {
            return;
        };
        if literals.next().is_some() {
            // More than one literal — not a simple fixed-arity operator.
            return;
        }

        let symbol = symbol.trim();
        if symbol.is_empty() {
            return;
        }

        let symbol_tokens = lex_symbol(symbol);
        if symbol_tokens.is_empty() {
            return;
        }

        // A custom symbol that re-lexes to a single built-in operator token
        // (e.g. redeclaring `+` or `*`) would shadow the hand-written builtin
        // precedence handling and risk wide-blast-radius regressions. The
        // builtin already parses those, so skip single-builtin-token symbols.
        if symbol_tokens.len() == 1 && is_builtin_operator_token(&symbol_tokens[0]) {
            return;
        }

        self.custom_operators.push(CustomOperator {
            symbol_tokens,
            kind: effective_kind,
            precedence: precedence.unwrap_or(65),
            expansion: effective_expansion,
            scope_ns,
        });
    }

    /// Register a CLOSED `notation` pattern: leading + trailing literal, every
    /// hole delimited by literals (no adjacent holes). Any other interleaving
    /// registers nothing and remains parse-only.
    ///
    /// The hole count may be **zero**: `notation "⊤" => Top.top` is a constant
    /// notation, and it is not a corner case — of the **827** single-line
    /// `notation` declarations in mathlib4 `43ad0e9d2`, **467 (56%) name no
    /// operand at all** (`⊤`, `⊥`, `ω`, `𝓟`, `σ`, …). Every one of them used to
    /// be rejected twice over — by a `pattern.len() < 3` floor and by a
    /// `vars.is_empty()` bail — so the declaration registered nothing and every
    /// later use died as `unknown operator or character '…'`. A zero-hole
    /// pattern is exactly the closed shape this function already models with
    /// the operand list empty; it needs no lambda (there is nothing to
    /// abstract) and it is atom-like, which the `precedence.unwrap_or(1024)`
    /// default already gives.
    fn register_custom_mixfix(
        &mut self,
        precedence: Option<u32>,
        pattern: &[NotationItem],
        expansion: &SurfaceExpr,
        scope_ns: Option<String>,
    ) {
        if !matches!(pattern.first(), Some(NotationItem::Literal(_)))
            || !matches!(pattern.last(), Some(NotationItem::Literal(_)))
        {
            return;
        }
        let mut items = Vec::with_capacity(pattern.len());
        let mut vars: Vec<String> = Vec::new();
        let mut prev_was_hole = false;
        for item in pattern {
            match item {
                NotationItem::Literal(lit) => {
                    let toks = lex_symbol(lit.trim());
                    if toks.is_empty() {
                        return;
                    }
                    items.push(MixfixItem::Literal(toks));
                    prev_was_hole = false;
                }
                NotationItem::Variable(v) => {
                    if prev_was_hole {
                        // Adjacent holes need application-boundary splitting —
                        // out of scope, keep parse-only.
                        return;
                    }
                    vars.push(v.clone());
                    items.push(MixfixItem::Hole);
                    prev_was_hole = true;
                }
            }
        }
        // The LEADING literal announces the notation at operand position, so it
        // must be a token the general grammar does not own: the unknown-symbol
        // class (`⌞`, …, lexed as `Error(UnexpectedChar)`) or `⟪` (`LDAngle`,
        // whose only builtin meaning is the two-element inner-product atom —
        // a registered user notation shadows it, matched BEFORE the atom
        // layer). A keyword-/ident-/delimiter-leading notation
        // (`notation "foo" x`, `notation "(" a ")"`) would shadow real atoms
        // and stays parse-only.
        let leads_with_free_symbol = matches!(
            items.first(),
            Some(MixfixItem::Literal(toks))
                if matches!(toks.first(), Some(TokenKind::Error(_) | TokenKind::LDAngle))
        );
        if !leads_with_free_symbol {
            return;
        }
        // A zero-hole notation abstracts nothing, and a zero-binder `Lambda`
        // is not a term — store the template itself.
        let template = if vars.is_empty() {
            expansion.clone()
        } else {
            let binders: Vec<SurfaceBinder> = vars
                .into_iter()
                .map(|v| SurfaceBinder::new(v, None, SurfaceBinderInfo::Explicit))
                .collect();
            SurfaceExpr::Lambda(expansion.span(), binders, Box::new(expansion.clone()))
        };
        self.custom_mixfixes.push(CustomMixfix {
            items,
            precedence: precedence.unwrap_or(1024),
            expansion: template,
            scope_ns,
        });
    }

    /// Whether any custom operator or mixfix notation is registered. Hot-path
    /// guard so the dedicated parsing layers are zero-overhead pass-throughs
    /// otherwise.
    pub(super) fn has_custom_operators(&self) -> bool {
        !self.custom_operators.is_empty() || !self.custom_mixfixes.is_empty()
    }

    /// Run `f` with `custom_min_prec` set to `level` — the Lean precedence of
    /// the operand slot `f` parses — restoring the previous context on exit
    /// (success AND error). The builtin chain wraps every right-operand parse
    /// with this so the custom layers know which declared operators may extend
    /// an operand at the current position.
    pub(super) fn with_custom_min_prec<T>(
        &mut self,
        level: u32,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let saved = self.custom_min_prec;
        self.custom_min_prec = level;
        let out = f(self);
        self.custom_min_prec = saved;
        out
    }

    /// Parse an operand at Lean precedence level `m` by entering the builtin
    /// chain at the loosest layer whose operators all bind at least as tightly
    /// as `m`. Used for custom-operator right operands (`infixl:n` ⇒ `n + 1`,
    /// `infixr:n`/`prefix:n` ⇒ `n`), so e.g. a `prefix:60` operand includes
    /// builtin `*` (70) and `+` (65) exactly as in Lean.
    fn expr_at_custom_level(&mut self, m: u32) -> Result<SurfaceExpr, ParseError> {
        let saved = self.custom_min_prec;
        self.custom_min_prec = m;
        let result = match m {
            // Each band narrows itself to `max(custom_min_prec, its floor)`,
            // which `m` has just set, so entering the band that OWNS `m` is
            // enough to admit exactly the operators at level `m` and tighter.
            0..=10 => self.very_low_custom_infix_expr(),
            11..=20 => self.pipe_custom_infix_expr(),
            21..=30 => self.iff_custom_infix_expr(),
            31..=35 => self.or_custom_infix_expr(),
            36..=50 => self.low_custom_infix_expr(),
            51..=59 => self.mid_custom_infix_expr(),
            60..=65 => self.add_custom_expr(),
            66..=67 => self.cons_expr(),
            68 => self.sup_expr(),
            69 => self.inf_expr(),
            70 => self.mul_expr(),
            71..=73 => self.smul_expr(),
            74..=75 => self.subst_expr(),
            76..=80 => self.comp_expr(),
            81..=82 => self.setprod_expr(),
            83..=90 => self.compose_expr(),
            91..=100 => self.map_expr(),
            _ => self.unary_expr(),
        };
        self.custom_min_prec = saved;
        result
    }

    /// The `add_expr` chain position with a custom-operator continuation band.
    ///
    /// A custom operator LOOSER than a builtin already applied to its left
    /// (`a * b ⧳ c` with `⧳` at 60) is refused by the tight layer inside the
    /// builtin's right-operand parse (60 < 71) and must instead take the
    /// completed builtin tree as its left operand. This band — sitting at the
    /// loosest arithmetic position — is where those operators are consumed,
    /// still guarded by the enclosing context level. Pass-through to
    /// `add_expr` when the file declares no notation.
    pub(super) fn add_custom_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.add_expr()?;
        if !self.has_custom_operators() {
            return Ok(left);
        }
        // Levels below 60 belong to the outer low-infix band. Consuming them
        // here would make them bind tighter than `+`, comparisons, and `∧`.
        let min = self.custom_min_prec.max(CUSTOM_ARITHMETIC_FLOOR);
        loop {
            if let Some(op) = self.match_custom_operator(NotationKind::Postfix) {
                if op.precedence < min {
                    break;
                }
                self.consume_custom_operator(&op);
                left = apply_operator(&op.expansion, left.span(), &[left]);
                continue;
            }
            if let Some(op) = self
                .match_custom_operator(NotationKind::Infixl)
                .or_else(|| self.match_custom_operator(NotationKind::Infixr))
                .or_else(|| self.match_custom_operator(NotationKind::Infix))
            {
                if op.precedence < min {
                    break;
                }
                self.consume_custom_operator(&op);
                let rhs_level = if matches!(op.kind, NotationKind::Infixr) {
                    op.precedence
                } else {
                    op.precedence + 1
                };
                let right = self.expr_at_custom_level(rhs_level)?;
                left = apply_operator(&op.expansion, left.span(), &[left, right]);
                self.reject_nonassoc_chain(&op)?;
                continue;
            }
            break;
        }
        Ok(left)
    }

    /// Custom-infix band 0–10, immediately outside `hom_expr` (`⟶`, 10).
    ///
    /// The loosest band: every builtin binary form in the chain binds at least
    /// as tightly, so nothing here ever needs re-association.
    pub(super) fn very_low_custom_infix_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_infix_band(0, 10, Self::hom_expr)
    }

    /// Custom-infix band 11–20, between `|>` (10) and `<|>`/`↔` (20).
    pub(super) fn pipe_custom_infix_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_infix_band(11, 20, Self::orelse_expr)
    }

    /// Custom-infix band 21–30, between `↔` (20) and `∨` (30).
    ///
    /// **The Mathlib hom-arrow band.** `→+`, `→*`, `→+*`, `↪`, `≃`, `≃*` (all
    /// 25), `⥤` (26) and their 60-odd siblings are declared here. `→` (25)
    /// sits BELOW this position in the hand-written chain even though it is
    /// looser than a level-26 operator, so the rotation in
    /// [`apply_operator_across_looser_tails`] repairs `C ⥤ D → E` to
    /// `(C ⥤ D) → E` while leaving `A →+ B → C` (`infixr:25`, right slot
    /// `term:25`) right-nested, exactly as Lean groups them.
    pub(super) fn iff_custom_infix_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_infix_band(21, 30, Self::or_expr)
    }

    /// Custom-infix band 31–35, between `∨` (30) and `∧` (35).
    pub(super) fn or_custom_infix_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_infix_band(31, 35, Self::and_expr)
    }

    /// Custom-infix band 36–50, between `∧` (35) and the `infix:50` relations.
    ///
    /// Comparisons and arithmetic bind at least as tightly as a level-50 custom
    /// relation, while `∧`/`&&` (35) bind looser. This is the band that owns
    /// the relation boundary, so it also carries the low-precedence postfix
    /// rejection and the level-50 non-chaining check.
    pub(super) fn low_custom_infix_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_infix_band(
            CUSTOM_LOW_INFIX_FLOOR,
            CUSTOM_LOW_INFIX_CEILING,
            Self::cmp_expr,
        )
    }

    /// Custom-infix band 51–59, between the `infix:50` relations and `>>=`
    /// (55).
    ///
    /// KNOWN GAP, recorded rather than papered over: `bind_expr` (`>>=`, 55),
    /// `bitor_expr` (`|||`, 55) and `bitxor_expr` (`^^^`, 59) sit BELOW this
    /// position in the hand-written chain, so a custom operator at 56–59 beside
    /// an unparenthesized monadic-bind or bitwise operand groups as if those
    /// builtins bound tighter than they do. That inversion is pre-existing
    /// (`seq_expr` at 60 already sits above `bitor_expr` at 55) and its Mathlib
    /// radius is zero: every out-of-band Mathlib infix in 51–59 is at level 51.
    pub(super) fn mid_custom_infix_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_infix_band(51, 59, Self::bind_core_expr)
    }

    /// One custom-infix band: parse an operand with `descend` (the builtin
    /// chain layer immediately below this position), then precedence-climb over
    /// every registered custom infix operator whose declared level falls in
    /// `floor..=ceiling` and is at least the ambient operand level
    /// ([`Parser::custom_min_prec`]).
    ///
    /// An operator outside the window is left alone: a looser one for a band
    /// higher in the chain, a tighter one having already been consumed by a
    /// band below. Together the six bands own every level from 0 up, so a
    /// declared precedence never has to fail closed for being "unmodeled".
    fn custom_infix_band(
        &mut self,
        floor: u32,
        ceiling: u32,
        descend: fn(&mut Self) -> Result<SurfaceExpr, ParseError>,
    ) -> Result<SurfaceExpr, ParseError> {
        let mut left = descend(self)?;
        if !self.has_custom_operators() {
            return Ok(left);
        }
        // The band that owns the 50 relation boundary is the one that has to
        // police the postfix floor and comparison non-chaining; it is on the
        // descent path of every expression, so nothing is skipped by keeping
        // the checks in one place.
        let owns_relation_boundary = ceiling == CUSTOM_LOW_INFIX_CEILING;
        let min = self.custom_min_prec.max(floor);
        let mut saw_level_50_custom = false;

        loop {
            if owns_relation_boundary {
                if let Some(op) = self.match_custom_operator(NotationKind::Postfix) {
                    if op.precedence < CUSTOM_ARITHMETIC_FLOOR {
                        return Err(ParseError::UnexpectedToken {
                            line: self.current_line(),
                            col: self.current().col as usize,
                            message: format!(
                                "custom postfix operator precedence {} is outside the modeled \
                                 postfix band (60+); use a supported precedence",
                                op.precedence
                            ),
                        });
                    }
                }
            }

            let Some(op) = self
                .match_custom_operator(NotationKind::Infixl)
                .or_else(|| self.match_custom_operator(NotationKind::Infixr))
                .or_else(|| self.match_custom_operator(NotationKind::Infix))
            else {
                break;
            };

            if op.precedence > ceiling || op.precedence < min {
                break;
            }

            let operator_line = self.current_line();
            let operator_col = self.current().col as usize;
            self.consume_custom_operator(&op);
            // Lean operand-slot levels: `infixl:n` is `term:n op term:(n+1)`,
            // `infixr:n` is `term:(n+1) op term:n`, non-associative `infix:n`
            // is `term:(n+1) op term:(n+1)`.
            let (lhs_level, rhs_level) = match op.kind {
                NotationKind::Infixl => (op.precedence, op.precedence + 1),
                NotationKind::Infixr => (op.precedence + 1, op.precedence),
                _ => (op.precedence + 1, op.precedence + 1),
            };
            let right = self.expr_at_custom_level(rhs_level)?;
            let left_endpoint = rightmost_relation_operand(&left, lhs_level);
            let right_endpoint = leftmost_relation_operand(&right, rhs_level);
            if self.is_unparenthesized_binder_arrow(left_endpoint)
                || self.is_unparenthesized_binder_arrow(right_endpoint)
                || is_generated_dependent_product(left_endpoint)
                || is_generated_dependent_product(right_endpoint)
            {
                return Err(ParseError::UnexpectedToken {
                    line: operator_line,
                    col: operator_col,
                    message: "low-precedence custom infix beside an unparenthesized binder arrow \
                              or dependent product is not modeled; add parentheses to make the \
                              intended scope explicit"
                        .to_string(),
                });
            }
            left = apply_operator_across_looser_tails(
                &op.expansion,
                left,
                right,
                lhs_level,
                rhs_level,
            );
            self.reject_nonassoc_chain(&op)?;
            saw_level_50_custom |= op.precedence == CUSTOM_LOW_INFIX_CEILING;
        }

        // Builtin comparison operators and level-50 custom relations are both
        // non-chainable at this boundary. `cmp_expr` has already returned, so
        // catch the inverse order here rather than accepting a real definition
        // for `a ~> b` and relegating the orphaned `= c` to recovery syntax.
        if saw_level_50_custom {
            if let Some(op) = self.comparison_op_spelling() {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current().col as usize,
                    message: format!(
                        "'{op}' cannot follow a level-50 custom infix without \
                         parentheses; comparison-class operators do not chain"
                    ),
                });
            }
        }

        Ok(left)
    }

    /// A binder-arrow Pi begins at its first binder, whereas an authored
    /// `forall`/`∀`/`Π` Pi begins at the quantifier token. The distinction lets
    /// `p ~> ∀ x, q` remain valid while rejecting the Lean-incompatible
    /// `p ~> (x : T) → q` grouping. A parenthesized Pi has `Paren` at the root
    /// and therefore passes through deliberately.
    fn is_unparenthesized_binder_arrow(&self, expr: &SurfaceExpr) -> bool {
        let SurfaceExpr::Pi(span, _, _) = expr else {
            return false;
        };
        !self.tokens.iter().any(|token| {
            token.span.start == span.start
                && matches!(token.kind, TokenKind::Forall | TokenKind::Pi)
        })
    }

    /// Expression layer for user-declared operators, sitting between
    /// `unary_expr` and `app_expr`. Consumption is guarded by the declared
    /// precedence versus the current operand level (`custom_min_prec`):
    /// operators at least as tight as the context are consumed here, with
    /// right operands re-entering the builtin chain at the operator's level;
    /// looser operators are left for the [`Self::add_custom_expr`] band (infix/
    /// postfix) or rejected loudly (prefix/mixfix — Lean's "unexpected token at
    /// this precedence level"). When nothing is registered this is a
    /// transparent pass-through to `app_expr`.
    pub(super) fn custom_op_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        if !self.has_custom_operators() {
            return self.app_expr();
        }
        // Low infix operators are intentionally left for
        // `low_custom_infix_expr`; consuming one beside applications here would
        // silently give it arithmetic/application precedence.
        let min = self.custom_min_prec.max(CUSTOM_ARITHMETIC_FLOOR);

        // Leading prefix operators: `∿ x` => `<expansion> x`, operand at the
        // operator's declared level (`prefix:60` swallows `*`-tight material).
        if let Some(op) = self.match_custom_operator(NotationKind::Prefix) {
            let start = self.current_span();
            if op.precedence < min {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: start.start,
                    message: format!(
                        "custom prefix operator of precedence {} cannot start an \
                         operand at precedence level {min} — parenthesize it",
                        op.precedence
                    ),
                });
            }
            self.consume_custom_operator(&op);
            let operand = self.expr_at_custom_level(op.precedence)?;
            return Ok(apply_operator(&op.expansion, start, &[operand]));
        }

        // Closed mixfix notation announced by its leading literal: `⟪a, b, c⟫`.
        // Several notations may share that literal (`‖e‖` / `‖e‖₊` / `‖e‖ₑ`),
        // so every match is tried, most specific first, with backtracking.
        let mixfix_candidates = self.matching_custom_mixfixes();
        if !mixfix_candidates.is_empty() {
            return self.parse_custom_mixfix_alternatives(&mixfix_candidates, min);
        }

        let mut left = self.app_expr()?;

        loop {
            // Postfix: `x ‼` => `<expansion> x`.
            if let Some(op) = self.match_custom_operator(NotationKind::Postfix) {
                if op.precedence < min {
                    break;
                }
                self.consume_custom_operator(&op);
                left = apply_operator(&op.expansion, left.span(), &[left]);
                continue;
            }

            // Infix (left- or right-associative). `infixl:n` parses its right
            // operand at `n + 1` (so the loop left-folds equal levels);
            // `infixr:n` at `n` (so the recursive operand right-nests).
            if let Some(op) = self
                .match_custom_operator(NotationKind::Infixl)
                .or_else(|| self.match_custom_operator(NotationKind::Infixr))
                .or_else(|| self.match_custom_operator(NotationKind::Infix))
            {
                if op.precedence < min {
                    break;
                }
                self.consume_custom_operator(&op);
                // `infixr:n` parses its right operand at `n`; `infixl:n` and the
                // non-associative `infix:n` at `n + 1`.
                let rhs_level = if matches!(op.kind, NotationKind::Infixr) {
                    op.precedence
                } else {
                    op.precedence + 1
                };
                let right = self.expr_at_custom_level(rhs_level)?;
                left = apply_operator(&op.expansion, left.span(), &[left, right]);
                self.reject_nonassoc_chain(&op)?;
                continue;
            }

            break;
        }

        Ok(left)
    }

    /// Non-associative `infix`: after one `a op b`, a following use of the SAME
    /// operator (`a op b op c`) is a loud parse error — Lean requires explicit
    /// parentheses. A no-op for `infixl`/`infixr`.
    fn reject_nonassoc_chain(&self, op: &CustomOperator) -> Result<(), ParseError> {
        if !matches!(op.kind, NotationKind::Infix) {
            return Ok(());
        }
        if let Some(next) = self.match_custom_operator(NotationKind::Infix) {
            if next.symbol_tokens == op.symbol_tokens {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "non-associative infix operator cannot be chained; \
                              add parentheses to disambiguate the intended grouping"
                        .to_string(),
                });
            }
        }
        Ok(())
    }

    /// Whether a registered notation's scope tag is active at the cursor:
    /// unscoped notation always is; `scoped` notation only while its
    /// declaring namespace is the current namespace, a dot-prefix ancestor of
    /// it, or activated by a parse-time `open` / `open scoped`.
    pub(super) fn custom_scope_active(&self, scope_ns: Option<&str>) -> bool {
        let Some(ns) = scope_ns else {
            return true;
        };
        if let Some(current) = self.notation_ns_stack.last() {
            if current == ns
                || (current.len() > ns.len()
                    && current.starts_with(ns)
                    && current.as_bytes()[ns.len()] == b'.')
            {
                return true;
            }
        }
        self.open_scoped_notation_ns.iter().any(|a| a == ns)
    }

    /// Enter a `namespace` block for scoped-notation tracking: push the full
    /// dotted path and remember the activation mark that
    /// [`Parser::exit_notation_namespace`] truncates back to.
    pub(super) fn enter_notation_namespace(&mut self, name: &str) -> usize {
        let full = match self.notation_ns_stack.last() {
            Some(parent) => format!("{parent}.{name}"),
            None => name.to_owned(),
        };
        self.notation_ns_stack.push(full);
        self.open_scoped_notation_ns.len()
    }

    /// Leave a `namespace` block: pop the path and drop `open` activations
    /// made inside the block.
    pub(super) fn exit_notation_namespace(&mut self, open_mark: usize) {
        self.notation_ns_stack.pop();
        self.open_scoped_notation_ns.truncate(open_mark);
    }

    /// Activate a namespace path for scoped custom notation (parse-time
    /// `open X` / `open scoped X`). Candidates are the path as written plus
    /// each enclosing-namespace qualification, mirroring Lean's
    /// `resolveNamespace` candidate set; activating a namespace with no
    /// scoped notation is a no-op.
    pub(super) fn activate_open_scoped_notation_path(&mut self, path: &[String]) {
        if path.is_empty() {
            return;
        }
        let joined = path.join(".");
        // Each stack entry is already a full cumulative path, so the stack IS
        // the prefix set to qualify against.
        let qualified: Vec<String> = self
            .notation_ns_stack
            .iter()
            .map(|prefix| format!("{prefix}.{joined}"))
            .collect();
        self.open_scoped_notation_ns.push(joined);
        self.open_scoped_notation_ns.extend(qualified);
    }

    /// The current length of the parse-time scoped-notation activation list,
    /// used by `open … in` to bound its activations to the body.
    pub(super) fn open_scoped_notation_mark(&self) -> usize {
        self.open_scoped_notation_ns.len()
    }

    /// Truncate the activation list back to a saved mark (end of an
    /// `open … in` body).
    pub(super) fn truncate_open_scoped_notation(&mut self, mark: usize) {
        self.open_scoped_notation_ns.truncate(mark);
    }

    /// Every registered mixfix whose LEADING literal matches the tokens at the
    /// cursor, MOST SPECIFIC FIRST.
    ///
    /// A leading literal does not identify a notation: mathlib4 declares three
    /// notations sharing `‖` at
    /// `Mathlib/Analysis/Normed/Group/Defs.lean:80-82` (`‖e‖`, `‖e‖₊`, `‖e‖ₑ`),
    /// and this used to `max_by_key` over the LEADING literal alone — a
    /// three-way tie at one token, resolved to whichever element `max_by_key`
    /// happened to return, with no way back. Exactly one of the three then
    /// parsed and the others died on their continuation literal: measured on
    /// `Mathlib/Analysis/Normed/Group/Basic.lean`, `‖e‖` alone parses
    /// **167/258** declarations, adding `‖e‖₊` drops it to **100/256**, and all
    /// three give **81/252** — the ambiguity costs 86 declarations in one file.
    ///
    /// The class is not one family: **469 of mathlib4's 827** single-line
    /// `notation` declarations share their leading literal with at least one
    /// sibling, across **134 distinct** leading literals (`⟪` alone leads 59).
    ///
    /// Specificity is the TOTAL literal-token count of the whole pattern, which
    /// is what distinguishes the family (`‖e‖` = 2, `‖e‖₊` = `‖e‖ₑ` = 3):
    /// try the longest spelling first so a shorter prefix cannot claim an input
    /// the longer one matches exactly. Ties keep registration order, and every
    /// candidate is tried, so the order only decides which of two equally
    /// specific notations wins an input both accept.
    fn matching_custom_mixfixes(&self) -> Vec<CustomMixfix> {
        let mut matches: Vec<CustomMixfix> = self
            .custom_mixfixes
            .iter()
            .filter(|mf| {
                self.custom_scope_active(mf.scope_ns.as_deref())
                    && match mf.items.first() {
                        Some(MixfixItem::Literal(toks)) => self.tokens_match_at_cursor(toks),
                        _ => false,
                    }
            })
            .cloned()
            .collect();
        // `sort_by_key` is stable, so equal-specificity candidates keep
        // registration order.
        matches.sort_by_key(|mf| std::cmp::Reverse(mixfix_literal_tokens(mf)));
        matches
    }

    /// Try each candidate in order, restoring the cursor between attempts, and
    /// return the first complete parse.
    ///
    /// Without this, `parse_custom_mixfix`'s continuation-literal mismatch was
    /// a hard error that ended the declaration: `‖n‖₊` reported
    /// `expected Error(UnexpectedChar('₊')) to continue custom notation, got Def`
    /// even though a registered notation matched it exactly.
    ///
    /// On total failure the error reported is the one from the attempt that got
    /// FURTHEST through the input, and the cursor is left there — a candidate
    /// that died on its first continuation token says less about what the user
    /// wrote than one that consumed three holes and then tripped.
    fn parse_custom_mixfix_alternatives(
        &mut self,
        candidates: &[CustomMixfix],
        min: u32,
    ) -> Result<SurfaceExpr, ParseError> {
        let start_pos = self.pos;
        let mut furthest: Option<(usize, ParseError)> = None;
        for mf in candidates {
            self.pos = start_pos;
            let attempt = if mf.precedence < min {
                Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!(
                        "custom notation of precedence {} cannot start an operand \
                         at precedence level {min} — parenthesize it",
                        mf.precedence
                    ),
                })
            } else {
                self.parse_custom_mixfix(mf)
            };
            match attempt {
                Ok(parsed) => return Ok(parsed),
                Err(err) => {
                    if furthest.as_ref().is_none_or(|(pos, _)| self.pos > *pos) {
                        furthest = Some((self.pos, err));
                    }
                }
            }
        }
        match furthest {
            Some((pos, err)) => {
                self.pos = pos;
                Err(err)
            }
            // `candidates` is non-empty at every call site.
            None => {
                self.pos = start_pos;
                Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "no custom notation matched at this position".to_string(),
                })
            }
        }
    }

    /// Parse a matched closed mixfix from its leading literal: consume each
    /// literal in sequence (loud error on a mismatched continuation token) and
    /// parse each hole as a full expression, then apply the expansion template
    /// to the operands.
    fn parse_custom_mixfix(&mut self, mf: &CustomMixfix) -> Result<SurfaceExpr, ParseError> {
        let start = self.current_span();
        let mut operands: Vec<SurfaceExpr> = Vec::new();
        let mut is_leading = true;
        for item in &mf.items {
            match item {
                MixfixItem::Literal(toks) => {
                    if is_leading {
                        // Already matched at the cursor by `match_custom_mixfix`.
                        for _ in toks {
                            self.advance();
                        }
                        is_leading = false;
                    } else {
                        for tok in toks {
                            if self.current_kind() == tok {
                                self.advance();
                            } else {
                                return Err(ParseError::UnexpectedToken {
                                    line: self.current_line(),
                                    col: self.current_span().start,
                                    message: format!(
                                        "expected {tok:?} to continue custom notation, \
                                         got {:?}",
                                        self.current_kind()
                                    ),
                                });
                            }
                        }
                    }
                }
                MixfixItem::Hole => operands.push(self.expr()?),
            }
        }
        Ok(apply_operator(&mf.expansion, start, &operands))
    }

    /// Return a registered operator of the given `kind` whose symbol matches the
    /// tokens at the current position, if any. Longest match wins so a
    /// multi-token symbol is preferred over any shorter overlap.
    fn match_custom_operator(&self, kind: NotationKind) -> Option<CustomOperator> {
        self.custom_operators
            .iter()
            .filter(|op| {
                op.kind == kind
                    && self.custom_scope_active(op.scope_ns.as_deref())
                    && self.tokens_match_at_cursor(&op.symbol_tokens)
            })
            .max_by_key(|op| op.symbol_tokens.len())
            .cloned()
    }

    /// Whether the token-kind sequence matches the upcoming tokens by value.
    fn tokens_match_at_cursor(&self, symbol_tokens: &[TokenKind]) -> bool {
        self.tokens_match_at_offset(symbol_tokens, 0)
    }

    /// Whether `symbol_tokens` matches the tokens starting at `peek_kind(offset)`.
    fn tokens_match_at_offset(&self, symbol_tokens: &[TokenKind], offset: usize) -> bool {
        symbol_tokens
            .iter()
            .enumerate()
            .all(|(i, tok)| self.peek_kind(offset + i) == Some(tok))
    }

    /// Whether the tokens at `offset` begin a registered *infix* or *postfix*
    /// operator, or a mixfix CONTINUATION literal (a separator/closer such as
    /// the `⟫` of `⟪a, b⟫`). Such a symbol is an operator/delimiter, never an
    /// application argument, so `app_expr` must stop before it — without this
    /// a hole's application spine would swallow the closing literal. Prefix
    /// operators and mixfix LEADING literals are excluded: they legitimately
    /// start an operand and are dispatched by `custom_op_expr`.
    pub(super) fn starts_custom_infix_or_postfix_at(&self, offset: usize) -> bool {
        if self.custom_operators.is_empty() && self.custom_mixfixes.is_empty() {
            return false;
        }
        self.custom_operators.iter().any(|op| {
            matches!(
                op.kind,
                NotationKind::Infixl
                    | NotationKind::Infixr
                    | NotationKind::Infix
                    | NotationKind::Postfix
            ) && self.custom_scope_active(op.scope_ns.as_deref())
                && self.tokens_match_at_offset(&op.symbol_tokens, offset)
        }) || self.custom_mixfixes.iter().any(|mf| {
            self.custom_scope_active(mf.scope_ns.as_deref())
                && mf.items.iter().skip(1).any(|item| {
                    matches!(item, MixfixItem::Literal(toks)
                        if self.tokens_match_at_offset(toks, offset))
                })
        })
    }

    /// Advance past a matched operator's symbol tokens.
    fn consume_custom_operator(&mut self, op: &CustomOperator) {
        for _ in 0..op.symbol_tokens.len() {
            self.advance();
        }
    }
}

/// Classify a `notation` pattern as a simple fixed-arity operator shape,
/// returning the mapped kind and the ordered operand variable names.
///
/// `a "sym" b` → infix (registered left-associative), `"sym" a` → prefix,
/// `a "sym"` → postfix. Any other interleaving (mixfix with two or more
/// literals, binder notations, a bare symbol with no operand) returns `None`
/// and is left parse-only.
fn classify_notation_shape(pattern: &[NotationItem]) -> Option<(NotationKind, Vec<String>)> {
    match pattern {
        [NotationItem::Variable(a), NotationItem::Literal(_), NotationItem::Variable(b)] => {
            Some((NotationKind::Infixl, vec![a.clone(), b.clone()]))
        }
        [NotationItem::Literal(_), NotationItem::Variable(a)] => {
            Some((NotationKind::Prefix, vec![a.clone()]))
        }
        [NotationItem::Variable(a), NotationItem::Literal(_)] => {
            Some((NotationKind::Postfix, vec![a.clone()]))
        }
        _ => None,
    }
}

/// Total number of literal TOKENS across a mixfix pattern — the specificity
/// key used to order overlapping candidates (`‖e‖` = 2, `‖e‖₊` = 3).
fn mixfix_literal_tokens(mf: &CustomMixfix) -> usize {
    mf.items
        .iter()
        .map(|item| match item {
            MixfixItem::Literal(toks) => toks.len(),
            MixfixItem::Hole => 0,
        })
        .sum()
}

/// Lex a notation symbol into its token-kind sequence, dropping the trailing
/// EOF. Returns empty if the symbol does not lex to any real token.
fn lex_symbol(symbol: &str) -> Vec<TokenKind> {
    Lexer::tokenize(symbol)
        .into_iter()
        .map(|t| t.kind)
        .filter(|k| !matches!(k, TokenKind::Eof))
        .collect()
}

/// Build `<expansion> arg0 arg1 ...`.
///
/// A NULLARY notation (`notation "∞" => Nat`) has no operands and no
/// abstracting lambda, so its expansion IS the term: applying it to an empty
/// argument list would mint `App(Nat, [])`, a spine the elaborator has no
/// reason to expect. Return the template unchanged instead.
fn apply_operator(expansion: &SurfaceExpr, start: Span, operands: &[SurfaceExpr]) -> SurfaceExpr {
    if operands.is_empty() {
        return expansion.clone();
    }
    let end = operands
        .last()
        .map_or_else(|| expansion.span(), SurfaceExpr::span);
    let span = start.merge(end);
    SurfaceExpr::App(
        span,
        Box::new(expansion.clone()),
        operands
            .iter()
            .cloned()
            .map(SurfaceArg::positional)
            .collect(),
    )
}

/// Whether a single token is a built-in operator already handled by the
/// hand-written precedence chain. Redeclaring such a one-token symbol must not
/// shadow the builtin.
fn is_builtin_operator_token(tok: &TokenKind) -> bool {
    matches!(
        tok,
        TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::Caret
            | TokenKind::Eq
            | TokenKind::Ne
            | TokenKind::BNe
            | TokenKind::Lt
            | TokenKind::Le
            | TokenKind::Gt
            | TokenKind::Ge
            | TokenKind::Arrow
            | TokenKind::Times
            | TokenKind::Oplus
            | TokenKind::ColonColon
            | TokenKind::And
            | TokenKind::Or
            | TokenKind::Iff
            | TokenKind::DoubleEq
            | TokenKind::Compose
            | TokenKind::Union
            | TokenKind::Inter
            | TokenKind::AmpAmp
            | TokenKind::PipePipe
            | TokenKind::BitAnd
            | TokenKind::BitOr
            | TokenKind::BitXor
            | TokenKind::ShiftL
            | TokenKind::ShiftR
    )
}
