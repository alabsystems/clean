// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Residual expression parsing: term constructs (exists, show, have, suffices,
//! record literals, struct update, set builder, list/array literals, open, set_option).
//!
//! The bulk of expression parsing has been split into submodules:
//! - `expr_operators.rs`: Operator precedence (expr through unary_expr)
//! - `expr_app.rs`: Application and atom expressions
//! - `expr_lambda_let.rs`: Lambda, let, if, forall, by, calc
//! - `expr_match.rs`: Match and pattern parsing
//! - `expr_do.rs`: Do notation
//! - `expr_binders.rs`: Binders, identifiers, levels, attributes

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse exists: ∃ x, P x
    pub(super) fn exists_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // `paren_guards` come from parenthesized bounded binders `∃ (x ∈ s), p`;
        // the trailing unparenthesized form `∃ x ∈ s, p` is handled below. For
        // `∃`, every guard is conjoined with the body:
        //   ∃ x ∈ S, P x   ≡  ∃ x, x ∈ S ∧ P x
        //   ∃ n > 0, P n   ≡  ∃ n, n > 0 ∧ P n
        let (binders, paren_guards) = self.quant_binders()?;

        let trailing_guard = match binders.last() {
            Some(last_binder) => self.try_bounded_guard(last_binder)?,
            None => None,
        };

        let raw_body = if trailing_guard.is_some() {
            self.expect(&TokenKind::Comma)?;
            self.expr()?
        } else if self.eat(&TokenKind::In) {
            // Filter quantifier: ∃ᶠ x in F, body (Mathlib Filter.Frequently)
            let _filter = self.arrow_expr()?;
            self.expect(&TokenKind::Comma)?;
            self.expr()?
        } else {
            self.expect(&TokenKind::Comma)?;
            self.expr()?
        };

        // Conjoin the guards with the body: trailing guard nearest the body,
        // then parenthesized guards in reverse binder order.
        let conj = |guard: SurfaceExpr, acc: SurfaceExpr| {
            let span = guard.span().merge(acc.span());
            SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "And".to_string())),
                vec![SurfaceArg::positional(guard), SurfaceArg::positional(acc)],
            )
        };
        let mut body = raw_body;
        if let Some(guard) = trailing_guard {
            body = conj(guard, body);
        }
        for guard in paren_guards.into_iter().rev() {
            body = conj(guard, body);
        }

        // Build nested Exists applications. Lean's `Exists : {α} → (α → Prop) →
        // Prop` takes the predicate as its ONLY explicit argument (α is implicit,
        // inferred from the binder type), so `∃ x : T, p` ⇒ `Exists (fun x : T =>
        // p)` — the binder type rides on the lambda, NOT a spurious positional
        // type argument (audit B3-exists-desugar).
        let mut result = body;
        for binder in binders.into_iter().rev() {
            let span = start_span.merge(result.span());
            result = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "Exists".to_string())),
                vec![SurfaceArg::positional(SurfaceExpr::Lambda(
                    span,
                    vec![binder],
                    Box::new(result),
                ))],
            );
        }

        Ok(result)
    }

    /// Parse the dependent-pair type binder: `Σ x : T, body`.
    ///
    /// Desugars to `Sigma (fun x : T => body)` — the type annotation is placed
    /// on the lambda binder (not passed as a separate positional argument as in
    /// `exists_body`) so `Sigma`'s implicit `{α}` is inferred from it. Multiple
    /// binders right-nest: `Σ x y : T, body` ≡ `Sigma (fun x : T => Sigma (fun
    /// y : T => body))`, mirroring Lean's iterated-binder Sigma notation.
    pub(super) fn sigma_body(
        &mut self,
        start_span: Span,
        head: &str,
    ) -> Result<SurfaceExpr, ParseError> {
        let binders = self.binders()?;
        self.expect(&TokenKind::Comma)?;
        let body = self.expr()?;

        // Build nested Sigma / PSigma applications, right-associatively.
        let mut result = body;
        for binder in binders.into_iter().rev() {
            let span = start_span.merge(result.span());
            result = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, head.to_string())),
                vec![SurfaceArg::positional(SurfaceExpr::Lambda(
                    span,
                    vec![binder],
                    Box::new(result),
                ))],
            );
        }

        Ok(result)
    }

    /// Parse unique exists: ∃! x, P x
    pub(super) fn exists_unique_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        // Parenthesized bounded binders `∃! (x ∈ s), p` contribute guards
        // conjoined with the body, matching the unparenthesized `∃! x ∈ s, p`:
        //   ∃! x ∈ S, P x   ≡  ∃! x, x ∈ S ∧ P x
        //   ∃! n > 0, P n   ≡  ∃! n, n > 0 ∧ P n
        let (binders, paren_guards) = self.quant_binders()?;

        let trailing_guard = match binders.last() {
            Some(last_binder) => self.try_bounded_guard(last_binder)?,
            None => None,
        };

        let raw_body = {
            self.expect(&TokenKind::Comma)?;
            self.expr()?
        };

        let conj = |guard: SurfaceExpr, acc: SurfaceExpr| {
            let span = guard.span().merge(acc.span());
            SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "And".to_string())),
                vec![SurfaceArg::positional(guard), SurfaceArg::positional(acc)],
            )
        };
        let mut body = raw_body;
        if let Some(guard) = trailing_guard {
            body = conj(guard, body);
        }
        for guard in paren_guards.into_iter().rev() {
            body = conj(guard, body);
        }

        // Build nested ExistsUnique applications. Mathlib's `ExistsUnique
        // (p : α → Prop)` takes the predicate as its ONLY explicit argument
        // (α implicit, inferred from the binder-type ascription on the lambda) —
        // same shape as `Exists`/`Sigma`, NOT a positional type argument.
        let mut result = body;
        for binder in binders.into_iter().rev() {
            let span = start_span.merge(result.span());
            result = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "ExistsUnique".to_string())),
                vec![SurfaceArg::positional(SurfaceExpr::Lambda(
                    span,
                    vec![binder],
                    Box::new(result),
                ))],
            );
        }

        Ok(result)
    }

    /// Parse a `show` term expression.
    ///
    /// Lean 4 admits two term-level forms (`Lean.Parser.Term.show`):
    /// - `show t from e` — ascribe the proof term `e` to type `t`
    /// - `show t by tac` — ascribe a `by` tactic block to type `t`
    ///
    /// Both desugar to the same `Ascription` node; only the justification
    /// (a plain term vs. a `ByTactic` block) differs.
    pub(super) fn show_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Parse the type `t`. A trailing `by` belongs to the `show` parser, not
        // to an application inside the type, so guard against `by` being read as
        // an application argument while we parse `t`.
        let prev_stop_at_by = self.stop_app_at_by;
        self.stop_app_at_by = true;
        let ty_result = self.expr();
        self.stop_app_at_by = prev_stop_at_by;
        let ty = ty_result?;

        // `show t by tac` — the goal is discharged by a tactic block.
        if self.check(&TokenKind::By) {
            let by_span = self.current_span();
            self.advance(); // consume `by`
            let expr = self.by_body(by_span);
            let span = start_span.merge(expr.span());
            return Ok(SurfaceExpr::Ascription(span, Box::new(expr), Box::new(ty)));
        }

        // `show t from e` — the goal is discharged by a proof term.
        self.expect(&TokenKind::From)?;
        let expr = self.expr()?;
        let span = start_span.merge(expr.span());
        Ok(SurfaceExpr::Ascription(span, Box::new(expr), Box::new(ty)))
    }

    /// Parse have expression in term position: `have h : P := proof; body`
    /// Equivalent to a let binding but for proof terms
    pub(super) fn have_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Column of the `have` keyword (just consumed by the caller, so it is the
        // token at `pos - 1`). Used for layout-aware value termination below.
        let have_col = self.let_keyword_col();

        // Anonymous-constructor destructuring `have ⟨a, b⟩ (: T)? := e; body`.
        // Lean desugars this to `match e with | ⟨a, b⟩ => body` (the
        // `have`-with-pattern form of `haveDecl`). Mirror `let ⟨a, b⟩ := e`
        // (`let_tuple_body`): parse the full anonymous-ctor pattern, the value
        // (layout-aware, like the named form), and the body, then build a
        // single-arm match. Routes through the anonymous-constructor pattern
        // remap so any single-constructor scrutinee (Prod/Sigma/Subtype/And/
        // Exists/struct) destructures. (B106)
        if matches!(self.current_kind(), TokenKind::LAngle) {
            let pat_span = self.current_span();
            let pattern = self.pattern()?;
            let ty_annot = if self.eat(&TokenKind::Colon) {
                Some(self.expr()?)
            } else {
                None
            };
            self.expect(&TokenKind::ColonEq)?;
            let val = self.parse_let_value_layout(have_col)?;
            let body = self.have_body_after_value()?;
            let scrut = match ty_annot {
                Some(ty) => SurfaceExpr::Ascription(pat_span, Box::new(val), Box::new(ty)),
                None => val,
            };
            let span = start_span.merge(body.span());
            let arm = SurfaceMatchArm {
                span: pat_span,
                pattern,
                body,
            };
            return Ok(SurfaceExpr::Match(span, None, Box::new(scrut), vec![arm]));
        }

        // Parse name (optional, could start with `:` for anonymous). An
        // anonymous `have : P := e` binds the hypothesis under the name `this`
        // in the continuation, matching Lean's `expandHave`
        // (`src/Lean/Elab/BuiltinNotation.lean`): a `haveIdLhs` with no binding
        // identifier defaults to `this`, so `have : P := e; this` resolves
        // `this` to the just-introduced proof. (Previously this defaulted to an
        // inaccessible `_h`, leaving `this` unbound.)
        let name = if matches!(self.current_kind(), TokenKind::Ident(_)) {
            self.ident()?
        } else {
            "this".to_string()
        };

        // Parse optional type annotation
        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.expr()?)
        } else {
            None
        };

        // Parse value with layout-aware termination (like `let`): a following
        // line that dedents to (or below) the `have` keyword's column begins the
        // *body*, not a continuation of the value. Using plain `self.expr()` here
        // greedily swallowed the newline-separated body.
        self.expect(&TokenKind::ColonEq)?;
        let val = self.parse_let_value_layout(have_col)?;

        let body = self.have_body_after_value()?;

        let span = start_span.merge(body.span());
        let binder = SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit);
        Ok(SurfaceExpr::Let(
            span,
            binder,
            Box::new(val),
            Box::new(body),
        ))
    }

    /// Parse the body of a term-mode `have` after its value.
    ///
    /// Lean 4 admits the body after either an explicit `;` separator OR a
    /// newline (layout), e.g.
    ///   have x : Nat := 3
    ///   ⟨x, x⟩
    /// Mirror `let_body_after_value` (minus `in`, which `have` does not use):
    /// accept `;`, a chained `let`/`have`, or any implicit-body-starting token
    /// on the next line. Shared by the named and anonymous-pattern have forms.
    fn have_body_after_value(&mut self) -> Result<SurfaceExpr, ParseError> {
        if self.eat(&TokenKind::Semicolon) {
            self.expr()
        } else if matches!(self.current_kind(), TokenKind::Let) {
            let let_span = self.current_span();
            self.advance();
            self.let_body(let_span)
        } else if matches!(self.current_kind(), TokenKind::Have) {
            let have_span = self.current_span();
            self.advance();
            self.have_body(have_span)
        } else if self.is_implicit_body_start() {
            self.implicit_let_body_expr()
        } else {
            Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `;` or a body expression after `have` binding, got {:?}",
                    self.current_kind()
                ),
            })
        }
    }

    /// Parse suffices expression in term position.
    ///
    /// Lean 4 admits two justification forms (`Lean.Parser.Term.suffices`):
    /// - `suffices h : P by tac; body` — the main goal follows from `h : P`
    ///   via a tactic block, and `body` proves `P`.
    /// - `suffices h : P from e; body` — the main goal follows from `h : P`
    ///   via the proof term `e`, and `body` proves `P`.
    ///
    /// Both desugar identically to `let h : P := body; <justification>`, where
    /// the justification (a `by` block or a plain term `e`) consumes `h`.
    pub(super) fn suffices_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Column of the `suffices` keyword (consumed by the caller, so it is the
        // token at `pos - 1`). Used as the layout reference so the `from`
        // justification's application stops at the newline-separated
        // continuation body (`optSemicolon term`) instead of swallowing it.
        let suffices_col = self
            .pos
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or_else(|| self.current().col, |t| t.col);

        // Parse name (optional)
        let name = if matches!(self.current_kind(), TokenKind::Ident(_))
            && !matches!(self.current_kind(), TokenKind::By)
        {
            self.ident()?
        } else {
            "_h".to_string()
        };

        // Parse type annotation (required for suffices). The type is a full
        // term (`suffices h : a = b from …`), not just an atom, so it must use
        // the operator grammar — a trailing `by`/`from` belongs to the
        // `suffices` justification, not to an application inside the type, so
        // guard `by` from being read as an application argument (mirrors
        // `show_body`; `from` is a keyword and already stops the app spine).
        let ty = if self.eat(&TokenKind::Colon) {
            let prev_stop_at_by = self.stop_app_at_by;
            self.stop_app_at_by = true;
            let ty_result = self.expr();
            self.stop_app_at_by = prev_stop_at_by;
            Some(ty_result?)
        } else {
            None
        };

        // Parse the justification: either `by tactic` or `from term`.
        // Parse a single tactic (not a full sequence), since the `;` after it
        // delimits the tactic block from the body expression. Without indentation
        // tracking (#1798), a single tactic is the safe parse boundary.
        let justification = if self.eat(&TokenKind::By) {
            let tac_span = self.current_span();
            match self.tactic() {
                Ok(tac) => {
                    let end = tac.span();
                    Some(Box::new(SurfaceExpr::ByTactic(
                        tac_span.merge(end),
                        vec![tac],
                    )))
                }
                Err(_) => {
                    // Graceful degradation: preserve parser-inserted sorry provenance.
                    Some(Box::new(SurfaceExpr::SyntheticSorry(tac_span)))
                }
            }
        } else if self.eat(&TokenKind::From) {
            // `suffices h : P from e; body` — the goal follows from the proof
            // term `e`, which may reference `h`. When the continuation `body`
            // follows on the next line without a `;`, it must not be swallowed
            // into `e`'s application spine: parse `e` under a layout keyed to the
            // `suffices` column so a newline-leading token at ≤ that column ends
            // the justification (Lean `optSemicolon term`). Same mechanism as
            // `parse_let_value_layout`.
            let saved_stop = self.stop_app_at_newline_outer_indent;
            self.push_indent_for(suffices_col, "suffices from justification");
            self.stop_app_at_newline_outer_indent = true;
            let just = self.expr();
            self.stop_app_at_newline_outer_indent = saved_stop;
            self.pop_indent();
            Some(Box::new(just?))
        } else {
            None
        };

        // Parse the body (the proof of P). Lean's grammar is
        // `suffices sufficesDecl optSemicolon term`: the continuation term
        // follows either after a `;` or on the next line without one, so the
        // separator is optional (probe term_sugar/p03 uses the newline form).
        self.eat(&TokenKind::Semicolon);
        let body = self.expr()?;

        let span = start_span.merge(body.span());
        let binder = SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit);

        // Represent as a let with the justification as the let-body:
        // suffices h : P by tac; proof   ≈ let h := proof; <by tac>
        // suffices h : P from e; proof   ≈ let h := proof; e
        if let Some(just) = justification {
            Ok(SurfaceExpr::Let(span, binder, Box::new(body), just))
        } else {
            // Without justification, just a simple let
            Ok(SurfaceExpr::Let(
                span,
                binder,
                Box::new(body),
                Box::new(SurfaceExpr::Ident(span, "_".to_string())),
            ))
        }
    }

    /// Parse record literal `{ field := value, ... }` or set builder `{ x | P x }`
    ///
    /// Supports:
    /// - Empty struct: `{}`
    /// - Set builder: `{x | P x}` → setOf (fun x => P x)
    /// - Field assignments: `{ x := val, y := val2 }`
    /// - Type annotation: `{ x := val : StructType }`
    /// - With-syntax: `{ s with x := newval }` (struct update)
    /// - Fallback: anything else returns Hole (finite sets `{A, B, C}`, etc.)
    pub(super) fn record_literal_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        // Empty struct literal: {}
        if self.check(&TokenKind::RBrace) {
            let end_span = self.current_span();
            self.advance();
            return Ok(SurfaceExpr::StructLit {
                span: start_span.merge(end_span),
                struct_type: None,
                base: None,
                fields: vec![],
            });
        }

        // Check for set builder notation: {x | P x} or {x : T | P x}
        // Pattern: identifier (optionally with type) followed by Pipe
        if self.is_set_builder_start() {
            return self.set_builder_body(start_span);
        }

        // Subtype: `{ x // p }` or `{ x : T // p }` → `Subtype (fun x : T => p)`
        // (Lean `Init/Notation.lean:575`). Detected by a top-level `//` separator.
        if self.is_subtype_start() {
            return self.subtype_body(start_span);
        }

        // Struct literal with field assignments AND bare-ident field
        // abbreviations: `{ x := v, ... }`, `{ a }` (≡ `{ a := a }`),
        // `{ a, b := 9 }`. A bare-ident brace list is Lean's structInst
        // field-abbreviation reading (`({a} : Q)` ⇒ `{ a := 7 }`), distinct from
        // a collection literal of non-ident elements (`{5}` ⇒ `singleton 5`).
        if self.is_struct_or_abbrev_field_start() || self.is_struct_field_path_start() {
            return self.parse_struct_literal_fields(start_span, None);
        }

        // Check for struct update syntax: {s with x := val, ...}
        if self.find_struct_update_with().is_some() {
            return self.parse_struct_update(start_span);
        }

        // Collection literal: `{a}` ⇒ `singleton a`, `{a, b, c}` ⇒
        // `insert a (insert b (singleton c))` (Lean `Init/NotationExtra.lean:337`,
        // right-nested). Reached when the elements are general terms, not the
        // field-abbreviation form handled above.
        self.collection_literal_body(start_span)
    }

    /// Whether the brace content begins a struct-literal field or a bare-ident
    /// field abbreviation: an identifier immediately followed by `:=` (an
    /// assignment `x := v`), or by `,`/`}` (an abbreviation `x` ≡ `x := x`).
    pub(super) fn is_struct_or_abbrev_field_start(&self) -> bool {
        matches!(self.current_kind(), TokenKind::Ident(_))
            && matches!(
                self.peek_kind(1),
                Some(TokenKind::ColonEq | TokenKind::Comma | TokenKind::RBrace)
            )
    }

    /// Whether the brace content is a subtype `{ ident (: T)? // p }`: an
    /// identifier followed (at brace depth 0) by a `//` separator before any
    /// closing `}`, `|`, or `:=`.
    pub(super) fn is_subtype_start(&self) -> bool {
        if !matches!(self.current_kind(), TokenKind::Ident(_)) {
            return false;
        }
        let mut depth: u32 = 0;
        for offset in 1..100 {
            match self.peek_kind(offset) {
                Some(TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket) => depth += 1,
                Some(TokenKind::RParen | TokenKind::RBracket) => depth = depth.saturating_sub(1),
                Some(TokenKind::RBrace) if depth > 0 => depth -= 1,
                Some(TokenKind::RBrace) => return false,
                Some(TokenKind::SlashSlash) if depth == 0 => return true,
                Some(TokenKind::Pipe | TokenKind::ColonEq) if depth == 0 => return false,
                None => return false,
                _ => {}
            }
        }
        false
    }

    /// Parse a subtype `{ x // p }` / `{ x : T // p }` into
    /// `Subtype (fun x : T => p)`.
    fn subtype_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let var_span = self.current_span();
        let var_name = self.ident()?;
        let var_ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };
        self.expect(&TokenKind::SlashSlash)?;
        let pred = self.expr()?;
        let end_span = self.expect(&TokenKind::RBrace)?.span;
        let span = start_span.merge(end_span);
        let binder = SurfaceBinder {
            name: var_name,
            span: var_span,
            ty: var_ty,
            default: None,
            info: SurfaceBinderInfo::Explicit,
        };
        let lambda = SurfaceExpr::Lambda(span, vec![binder], Box::new(pred));
        Ok(SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(start_span, "Subtype".to_string())),
            vec![SurfaceArg::positional(lambda)],
        ))
    }

    /// Parse a collection literal `{ a }` / `{ a, b, c }` into a right-nested
    /// `singleton` / `insert` chain (Lean `{term,+}`, no trailing comma).
    fn collection_literal_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let mut elems = vec![self.expr()?];
        while self.eat(&TokenKind::Comma) {
            elems.push(self.expr()?);
        }
        let end_span = self.expect(&TokenKind::RBrace)?.span;
        let span = start_span.merge(end_span);
        // Right-nested: insert a (insert b (singleton c)).
        let mut iter = elems.into_iter().rev();
        let last = iter.next().unwrap_or(SurfaceExpr::Hole(span));
        let mut result = SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(start_span, "singleton".to_string())),
            vec![SurfaceArg::positional(last)],
        );
        for elem in iter {
            result = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(start_span, "insert".to_string())),
                vec![SurfaceArg::positional(elem), SurfaceArg::positional(result)],
            );
        }
        Ok(result)
    }

    /// Parse a struct literal with field assignments.
    ///
    /// Supports Lean's `structInstLVal` field paths (`{ o with inner.v := 3 }`,
    /// `Lean/Parser/Term.lean`): a dotted field path assigns into a nested
    /// subobject. These are desugared here, at parse time, into the nested
    /// structure-update form Lean produces during elaboration — grouping fields
    /// by their leading component and recursing with `base.field` as the inner
    /// source (`{ o with inner.v := 3 }` ⇒ `{ o with inner := { o.inner with v
    /// := 3 } }`). The common single-component case is unchanged.
    fn parse_struct_literal_fields(
        &mut self,
        start_span: Span,
        base: Option<Box<SurfaceExpr>>,
    ) -> Result<SurfaceExpr, ParseError> {
        // Parse field assignments, bare-ident abbreviations, and dotted paths.
        let mut raw_fields: Vec<(Span, Vec<String>, SurfaceExpr)> = Vec::new();
        let mut any_nested = false;
        while self.is_struct_or_abbrev_field_start() || self.is_struct_field_path_start() {
            let field_span = self.current_span();
            let path = self.parse_struct_field_path()?;
            if path.len() > 1 {
                any_nested = true;
            }
            let field_val = if self.eat(&TokenKind::ColonEq) {
                self.struct_field_value_expr()?
            } else {
                // Bare-ident abbreviation: `x` ≡ `x := x` (single component).
                SurfaceExpr::Ident(field_span, path[path.len() - 1].clone())
            };

            raw_fields.push((field_span, path, field_val));

            // Comma between fields is optional
            self.eat(&TokenKind::Comma);
        }

        // Optional ellipsis `..` (Lean structInst `optEllipsis`): remaining
        // fields are filled by defaults / elaboration. Nothing to record at the
        // surface level — the explicit fields already carry the information.
        self.eat(&TokenKind::DotDot);

        // Check for type annotation: `{ ... : StructType }`
        let struct_type = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        let end_span = self.expect(&TokenKind::RBrace)?.span;
        let span = start_span.merge(end_span);

        if !any_nested {
            // Fast path: every field is a single component — produce exactly the
            // same tree as before (no behavioral change for existing literals).
            let fields = raw_fields
                .into_iter()
                .map(|(span, mut path, val)| SurfaceFieldAssign {
                    span,
                    name: path.pop().unwrap_or_default(),
                    val,
                })
                .collect();
            return Ok(SurfaceExpr::StructLit {
                span,
                struct_type,
                base,
                fields,
            });
        }

        Ok(build_nested_struct_lit(
            base.map(|b| *b),
            raw_fields,
            struct_type,
            span,
        ))
    }

    /// Parse a struct-literal field path: `ident (. ident)*`.
    fn parse_struct_field_path(&mut self) -> Result<Vec<String>, ParseError> {
        let mut path = vec![self.ident()?];
        while self.check(&TokenKind::Dot) && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
        {
            self.advance(); // consume '.'
            path.push(self.ident()?);
        }
        Ok(path)
    }

    /// Whether the brace content begins a dotted struct-instance field path
    /// (`inner.v := 3`): an identifier, then one or more `.ident` segments, then
    /// a `:=` (at depth 0, before any `,`/`}`/`|`). Distinguishes a field path
    /// from a collection element like `{ Foo.bar }` (no `:=`).
    pub(super) fn is_struct_field_path_start(&self) -> bool {
        if !matches!(self.current_kind(), TokenKind::Ident(_)) {
            return false;
        }
        // Require at least one `.ident` segment (otherwise the existing
        // single-ident detector handles it).
        if !matches!(self.peek_kind(1), Some(TokenKind::Dot)) {
            return false;
        }
        let mut offset = 1;
        loop {
            match self.peek_kind(offset) {
                Some(TokenKind::Dot)
                    if matches!(self.peek_kind(offset + 1), Some(TokenKind::Ident(_))) =>
                {
                    offset += 2;
                }
                Some(TokenKind::ColonEq) => return true,
                _ => return false,
            }
        }
    }

    /// Parse struct update syntax: `{ s with x := val, ... }`
    fn parse_struct_update(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Parse the base expression (everything up to `with`)
        let base_expr = self.struct_update_base_expr()?;

        // Consume the `with` keyword
        self.expect(&TokenKind::With)?;

        // Parse field assignments (may be empty for `{ s with }`)
        self.parse_struct_literal_fields(start_span, Some(Box::new(base_expr)))
    }

    /// Parse the base expression in a struct update, stopping before `with`.
    /// This handles expressions like `s`, `foo.bar`, `f x`, etc.
    fn struct_update_base_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Parse atoms and applications until we hit `with`
        // Start with a single atom
        let mut expr = self.atom_expr()?;

        // Allow projections: s.field.subfield
        while self.check(&TokenKind::Dot) {
            if self.peek_kind(1) == Some(&TokenKind::With) {
                // .with is not a projection, stop here
                break;
            }
            self.advance(); // consume dot
            let proj_span = self.current_span();
            let field_name = self.ident()?;
            expr = SurfaceExpr::Proj(proj_span, Box::new(expr), Projection::Named(field_name));
        }

        // Allow simple function application: f x y (but stop before `with`)
        loop {
            // Stop if next token is `with`
            if self.check(&TokenKind::With) {
                break;
            }
            // Stop if we hit end of brace content
            if self.check(&TokenKind::RBrace) {
                break;
            }
            // Try to parse another argument using atom_expr
            if !self.is_atom_start() {
                break;
            }
            let arg = self.atom_expr()?;
            let span = expr.span().merge(arg.span());
            expr = SurfaceExpr::App(span, Box::new(expr), vec![SurfaceArg::positional(arg)]);
        }

        Ok(expr)
    }

    /// Check if brace content is struct update syntax: `{ expr with field := val ... }`
    /// Returns the offset to the `with` keyword if found, None otherwise.
    pub(super) fn find_struct_update_with(&self) -> Option<usize> {
        // Look for `with` keyword followed by field assignment pattern
        // Track bracket/brace/paren depth to avoid matching `with` inside nested groups
        let mut depth: u32 = 0;
        for offset in 0..100 {
            match self.peek_kind(offset) {
                Some(TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket) => {
                    depth += 1;
                }
                Some(TokenKind::RParen | TokenKind::RBracket) => {
                    depth = depth.saturating_sub(1);
                }
                Some(TokenKind::RBrace) if depth > 0 => depth -= 1,
                Some(TokenKind::RBrace) => return None, // Closing our brace without finding `with`
                Some(TokenKind::With) if depth == 0 => {
                    // Found `with` at top level - check if followed by a field
                    // assignment: `with <ident> :=` (simple) or `with <ident> .`
                    // (a dotted `structInstLVal` path, `{ o with inner.v := 3 }`).
                    if let Some(TokenKind::Ident(_)) = self.peek_kind(offset + 1) {
                        if matches!(
                            self.peek_kind(offset + 2),
                            Some(TokenKind::ColonEq | TokenKind::Dot)
                        ) {
                            return Some(offset);
                        }
                    }
                    // Also accept `with }` for update with no field changes (rare but valid)
                    if self.peek_kind(offset + 1) == Some(&TokenKind::RBrace) {
                        return Some(offset);
                    }
                    // `with` not followed by field pattern, continue searching
                }
                None => return None,
                _ => {}
            }
        }
        None
    }

    /// Check if current position looks like set builder notation: {x | P} or {x : T | P}
    pub(super) fn is_set_builder_start(&self) -> bool {
        // Must start with identifier
        if !matches!(self.current_kind(), TokenKind::Ident(_)) {
            return false;
        }
        // Check what follows the identifier
        match self.peek_kind(1) {
            // {x | ...} - direct pipe after identifier
            Some(TokenKind::Pipe) => true,
            // {x : T | ...} - typed binder, or {x ∈ s | ...} - separation
            // (`Set.sep`): both need a scan for a top-level pipe before the
            // closing brace (and must reject `:=` record fields).
            Some(TokenKind::Colon | TokenKind::Elem) => {
                // Scan ahead looking for Pipe before RBrace or ColonEq
                // Track bracket/brace/paren depth to avoid matching pipes inside nested groups
                let mut depth: u32 = 0;
                for offset in 2..100 {
                    match self.peek_kind(offset) {
                        Some(TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket) => {
                            depth += 1;
                        }
                        Some(TokenKind::RParen | TokenKind::RBracket) => {
                            depth = depth.saturating_sub(1);
                        }
                        Some(TokenKind::RBrace) if depth > 0 => depth -= 1,
                        Some(TokenKind::RBrace) => return false, // Closing our brace
                        Some(TokenKind::Pipe) if depth == 0 => return true,
                        Some(TokenKind::ColonEq) if depth == 0 => return false,
                        None => return false,
                        _ => {}
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Parse set builder notation: {x | P x} → setOf (fun x => P x)
    pub(super) fn set_builder_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Parse the binder: x or (x : T)
        let var_span = self.current_span();
        let var_name = self.ident()?;

        // Optional type annotation `: T`, or a membership constraint `∈ s`
        // for separation notation `{x ∈ s | p}`. (Both stop before the pipe,
        // since `self.expr()` does not consume a top-level `|`.)
        let mut var_ty = None;
        let mut membership_set = None;
        if self.eat(&TokenKind::Colon) {
            var_ty = Some(self.expr()?);
        } else if self.eat(&TokenKind::Elem) {
            membership_set = Some(self.expr()?);
        }

        // Expect the pipe separator
        self.expect(&TokenKind::Pipe)?;

        // Parse the predicate
        let pred = self.expr()?;

        // Expect closing brace
        let end_span = self.expect(&TokenKind::RBrace)?.span;
        let span = start_span.merge(end_span);

        // For separation `{x ∈ s | p}` the lambda body is `x ∈ s ∧ p`, i.e.
        // `And (Membership.mem s x) p` — identical to hand-writing
        // `{x | x ∈ s ∧ p}` (note the `∈` argument swap: `Membership.mem s x`).
        // Plain `{x | p}` / `{x : T | p}` keep the predicate as-is.
        let body_pred = if let Some(set_expr) = membership_set {
            let x_ident = SurfaceExpr::Ident(var_span, var_name.clone());
            let mem = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(var_span, "Membership.mem".to_string())),
                vec![
                    SurfaceArg::positional(set_expr),
                    SurfaceArg::positional(x_ident),
                ],
            );
            SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(var_span, "And".to_string())),
                vec![SurfaceArg::positional(mem), SurfaceArg::positional(pred)],
            )
        } else {
            pred
        };

        // Build: setOf (fun x => body) or setOf (fun (x : T) => body)
        let binder = SurfaceBinder {
            name: var_name,
            span: var_span,
            ty: var_ty.map(Box::new),
            default: None,
            info: SurfaceBinderInfo::Explicit,
        };

        let lambda = SurfaceExpr::Lambda(span, vec![binder], Box::new(body_pred));
        let setof = SurfaceExpr::Ident(span, "setOf".to_string());

        Ok(SurfaceExpr::App(
            span,
            Box::new(setof),
            vec![SurfaceArg::positional(lambda)],
        ))
    }

    /// Parse a struct field value expression.
    ///
    /// Struct-literal and struct-update field values accept the full
    /// expression grammar, including binary operators (`+`, `-`, `*`, etc.),
    /// `match`/`if`/`do`, and ascriptions. Earlier iterations restricted
    /// this to arrow+application only; that dropped expressions like
    /// `{ c with value := c.value + 1 }` (#3517) into the parser's
    /// skip-to-next-decl recovery branch, silently discarding the
    /// surrounding `def`.
    ///
    /// The `in_struct_field` flag is set so that `app_expr` stops at
    /// `ident :=` patterns, preserving the comma-less Lean 4 style
    /// `{ x := 1 y := 2 }` where `y` would otherwise be misparsed as
    /// an argument of the preceding value.
    ///
    /// `self.expr()` otherwise terminates at the tokens that separate
    /// struct fields (`,`, `:`, `}`): top-level `expr` only consumes
    /// commas/colons/rbraces inside explicit bracketed constructs
    /// (lists, tuples, parens, ascriptions). None of those constructs
    /// are entered from a struct-field value position, so full `expr`
    /// is safe here.
    pub(super) fn struct_field_value_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let saved = self.in_struct_field;
        self.in_struct_field = true;
        let result = self.expr();
        self.in_struct_field = saved;
        result
    }

    /// Parse `open Foo in expr` / `open scoped Foo in expr` expression form
    /// (scoping only). `open scoped X in <term>` brings namespace `X`'s scoped
    /// notations/instances into scope for the inner term's elaboration; Mathlib
    /// uses it heavily in `Decidable`-backed proofs (`open scoped Classical in
    /// Decidable.…`). The opened-namespace wiring is handled by the `open`
    /// command machinery (B13); here we parse the full form so the term does not
    /// wall the file.
    pub(super) fn open_expr_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Optional `scoped` keyword: `open scoped X in <term>`.
        let scoped = self.eat(&TokenKind::Scoped);
        // Consume one or more module paths (with optional selective names).
        // Preserve them (do NOT discard) so the elaborator can open the
        // namespaces for the sub-term's name/instance resolution.
        let mut paths = Vec::new();
        loop {
            if !matches!(self.current_kind(), TokenKind::Ident(_)) {
                break;
            }
            let path = self.module_path()?;

            // Optional selective names: `open Nat (add mul) in …`.
            let mut names = Vec::new();
            if self.eat(&TokenKind::LParen) {
                while self.is_ident_like() {
                    names.push(self.ident_like()?);
                }
                self.expect(&TokenKind::RParen)?;
            }

            paths.push(OpenPath {
                path,
                names,
                hiding: Vec::new(),
                renaming: Vec::new(),
            });

            if self.check(&TokenKind::In) || !matches!(self.current_kind(), TokenKind::Ident(_)) {
                break;
            }
        }

        self.expect(&TokenKind::In)?;
        let body = self.expr()?;
        let span = start_span.merge(body.span());

        // Preserve the opened namespaces (and the `scoped` flag) rather than
        // desugaring to an `App(Ident("open"), …)` marker that discarded the
        // path and left `open` to resolve as an unknown identifier. The
        // elaborator opens `paths` for `body`'s name/instance resolution and
        // pops the scope afterward (mirrors `SurfaceDecl::Open`).
        Ok(SurfaceExpr::OpenIn {
            span,
            paths,
            scoped,
            body: Box::new(body),
        })
    }

    /// Parse list literal: [a, b, c]
    pub(super) fn list_literal_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        // Empty list
        if self.eat(&TokenKind::RBracket) {
            return Ok(SurfaceExpr::Ident(start_span, "List.nil".to_string()));
        }

        // Bracket notation: [≠], [<], [>] etc. — Part of #8, Part of #2550
        // Lean 4 neighborhood filters like 𝓝[≠] place a bare operator inside
        // brackets. Parse as a special identifier so the surrounding
        // application (e.g. 𝓝[≠] 0) succeeds.
        if matches!(
            self.current_kind(),
            TokenKind::Ne
                | TokenKind::Lt
                | TokenKind::Gt
                | TokenKind::Le
                | TokenKind::Ge
                | TokenKind::Eq
        ) && matches!(self.peek_kind(1), Some(TokenKind::RBracket))
        {
            let op_name = match self.current_kind() {
                TokenKind::Ne => "Ne",
                TokenKind::Lt => "Lt",
                TokenKind::Gt => "Gt",
                TokenKind::Le => "Le",
                TokenKind::Ge => "Ge",
                TokenKind::Eq => "Eq",
                _ => unreachable!("bracket op matched non-comparison token"),
            };
            self.advance(); // consume operator
            let end_span = self.current_span();
            self.advance(); // consume ]
            return Ok(SurfaceExpr::Ident(
                start_span.merge(end_span),
                format!("bracketOp.{op_name}"),
            ));
        }

        let mut elems = Vec::new();
        elems.push(self.expr()?);

        // Named instance bracket: [name : Type] — Part of #8, Part of #2550
        // In Lean 4, `[inst : Mul S]` inside a type expression is an instance
        // binder, not a list literal. Parse as ascription so surrounding
        // code (e.g., `(S : Type) → [inst : Mul S] → Prop`) succeeds.
        if self.check(&TokenKind::Colon) && elems.len() == 1 {
            self.advance(); // consume :
            let ty = self.expr()?;
            let end_span = self.expect(&TokenKind::RBracket)?.span;
            return Ok(SurfaceExpr::Ascription(
                start_span.merge(end_span),
                Box::new(elems.into_iter().next().expect("len==1")),
                Box::new(ty),
            ));
        }

        while self.eat(&TokenKind::Comma) {
            if self.check(&TokenKind::RBracket) {
                break;
            }
            elems.push(self.expr()?);
        }
        let end_span = self.expect(&TokenKind::RBracket)?.span;

        // Build List.cons chain ending with List.nil
        let mut result = SurfaceExpr::Ident(start_span.merge(end_span), "List.nil".to_string());
        for elem in elems.into_iter().rev() {
            let span = start_span.merge(elem.span()).merge(result.span());
            result = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "List.cons".to_string())),
                vec![SurfaceArg::positional(elem), SurfaceArg::positional(result)],
            );
        }

        Ok(result)
    }

    /// Parse array literal: `#[a, b, c]`.
    ///
    /// Desugars to `Array.mk (List.cons a (List.cons b (List.cons c
    /// List.nil)))`. The single-field `Array` constructor is
    /// `Array.mk {α} (toList : List α)`, so an array literal is exactly the
    /// backing `List` wrapped in `Array.mk`. The empty literal `#[]`
    /// desugars to `Array.mk List.nil`.
    ///
    /// A previous version applied `Array.mk` to the elements *positionally*
    /// (`Array.mk a b c`), which is under-/mis-applied against the real
    /// one-argument constructor: `#[]` left `Array.mk` under-applied (leaking
    /// a free variable) and `#[1,2,3]` type-mismatched (elements passed where
    /// a `List` was expected). Building the backing `List` first fixes both.
    pub(super) fn array_literal_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        let mut elems = Vec::new();

        if !self.check(&TokenKind::RBracket) {
            elems.push(self.expr()?);
            while self.eat(&TokenKind::Comma) {
                if self.check(&TokenKind::RBracket) {
                    break;
                }
                elems.push(self.expr()?);
            }
        }

        let end_span = self.expect(&TokenKind::RBracket)?.span;
        let span = start_span.merge(end_span);

        // Build the backing `List.cons`/`List.nil` chain (identical structure
        // to `list_literal_body`), then wrap it in the single-field `Array.mk`.
        let mut backing = SurfaceExpr::Ident(span, "List.nil".to_string());
        for elem in elems.into_iter().rev() {
            let elem_span = span.merge(elem.span()).merge(backing.span());
            backing = SurfaceExpr::App(
                elem_span,
                Box::new(SurfaceExpr::Ident(elem_span, "List.cons".to_string())),
                vec![
                    SurfaceArg::positional(elem),
                    SurfaceArg::positional(backing),
                ],
            );
        }

        Ok(SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(span, "Array.mk".to_string())),
            vec![SurfaceArg::positional(backing)],
        ))
    }

    /// Parse big operator expression: ∑/∏/∫/⨍ binder (in S | ∈ S | : T), body
    ///
    /// Lean 4 big operator notation (Mathlib):
    /// - `∑ x in S, body`  → `Finset.sum S (fun x => body)`
    /// - `∑ x ∈ S, body`   → `Finset.sum S (fun x => body)`
    /// - `∑ x : T, body`   → `tsum (fun (x : T) => body)`
    /// - `∑ x, body`       → `tsum (fun x => body)`
    /// - `∏`, `∫`, `⨍` follow the same structure with different target names
    pub(super) fn bigop_body(
        &mut self,
        start_span: Span,
        op_name: &str,
    ) -> Result<SurfaceExpr, ParseError> {
        // Determine desugaring target names based on operator
        let (finite_fn, infinite_fn) = match op_name {
            "∑" | "BigSum" => ("Finset.sum", "tsum"),
            "∏" | "BigProd" => ("Finset.prod", "tprod"),
            "∫" | "Integral" => ("MeasureTheory.integral", "MeasureTheory.integral"),
            "⨍" | "FintAvg" => ("MeasureTheory.laverage", "MeasureTheory.laverage"),
            "⋃" | "BigUnion" => ("Set.iUnion", "Set.iUnion"),
            "⋂" | "BigInter" => ("Set.iInter", "Set.iInter"),
            _ => ("Finset.sum", "tsum"),
        };

        // Parse binder(s) — same as forall/exists
        let mut binders = self.binders()?;

        // Handle bare `: T` type annotation after untyped binders.
        // `∑ x : T, body` means x ranges over type T.
        // `∑ ⟨i, j⟩ : T, body` means the destructured pair ranges over T.
        if binders.iter().all(|b| b.ty.is_none()) && self.check(&TokenKind::Colon) {
            self.advance(); // consume :
            let ty = self.arrow_expr()?;
            let ty = Box::new(ty);
            for b in &mut binders {
                b.ty = Some(ty.clone());
            }
        }

        // Check for domain constraint after binders
        let (domain, use_finite) = if self.eat(&TokenKind::In) {
            // `BIGOP x in S, body` — explicit Finset domain
            let domain = self.arrow_expr()?;
            (Some(domain), true)
        } else if self.check(&TokenKind::Elem) {
            // `BIGOP x ∈ S, body` — membership domain (same as `in`)
            self.advance();
            let domain = self.arrow_expr()?;
            (Some(domain), true)
        } else if let Some(last_binder) = binders.last() {
            // Check for bounded guard: `BIGOP x ≥ n, body` etc.
            if let Some(guard) = self.try_bounded_guard(last_binder)? {
                // Bounded big op: treat guard as a filter condition
                // Desugar as finite with a Finset.filter or just pass through
                (Some(guard), true)
            } else {
                (None, false)
            }
        } else {
            (None, false)
        };

        self.expect(&TokenKind::Comma)?;
        let body = self.expr()?;

        // Build the lambda: fun binder => body
        let body_span = body.span();
        let lambda_binders: Vec<SurfaceBinder> = binders
            .into_iter()
            .map(|b| SurfaceBinder {
                span: b.span,
                name: b.name,
                ty: b.ty,
                default: None,
                info: b.info,
            })
            .collect();
        let lambda =
            SurfaceExpr::Lambda(start_span.merge(body_span), lambda_binders, Box::new(body));

        let span = start_span.merge(body_span);

        if let Some(domain) = domain {
            if use_finite {
                // Finite: fn_name domain (fun x => body)
                Ok(SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(span, finite_fn.to_string())),
                    vec![
                        SurfaceArg::positional(domain),
                        SurfaceArg::positional(lambda),
                    ],
                ))
            } else {
                // Infinite with guard: fn_name (fun x => body)
                Ok(SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(span, infinite_fn.to_string())),
                    vec![SurfaceArg::positional(lambda)],
                ))
            }
        } else {
            // No domain: infinite_fn (fun x => body)
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, infinite_fn.to_string())),
                vec![SurfaceArg::positional(lambda)],
            ))
        }
    }

    /// Parse `set_option` ... in expr expression form
    pub(super) fn set_option_expr(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let name = self.qualified_ident()?;

        let value = if self.check(&TokenKind::In) {
            None
        } else {
            Some(self.expr()?)
        };

        self.expect(&TokenKind::In)?;
        let body = self.expr()?;

        let name_expr = SurfaceExpr::Ident(start_span, name);
        let value_expr = value.unwrap_or(SurfaceExpr::Hole(start_span));
        let span = start_span.merge(body.span());
        Ok(SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(start_span, "set_option".to_string())),
            vec![
                SurfaceArg::positional(name_expr),
                SurfaceArg::positional(value_expr),
                SurfaceArg::positional(body),
            ],
        ))
    }
}

/// Desugar a struct-instance literal whose fields may carry dotted paths into
/// the nested structure-update form (Lean `StructInst` field grouping): fields
/// are grouped by their leading component (order-preserving), and any group
/// whose members all have a remaining path is emitted as a nested
/// `{ base.field with <rest> := … }`. A member with an empty remaining path is a
/// direct assignment to that field and takes precedence for its group.
fn build_nested_struct_lit(
    base: Option<SurfaceExpr>,
    fields: Vec<(Span, Vec<String>, SurfaceExpr)>,
    struct_type: Option<Box<SurfaceExpr>>,
    span: Span,
) -> SurfaceExpr {
    // Group by leading path component, preserving first-seen order.
    let mut groups: Vec<(String, Span, Vec<(Span, Vec<String>, SurfaceExpr)>)> = Vec::new();
    for (fspan, mut path, val) in fields {
        let first = path.remove(0);
        if let Some(group) = groups.iter_mut().find(|(name, _, _)| *name == first) {
            group.2.push((fspan, path, val));
        } else {
            groups.push((first, fspan, vec![(fspan, path, val)]));
        }
    }

    let assigns = groups
        .into_iter()
        .map(|(first, gspan, members)| {
            // A direct assignment (empty remaining path) wins for this field.
            if let Some((_, _, val)) = members.iter().find(|(_, rest, _)| rest.is_empty()) {
                return SurfaceFieldAssign {
                    span: gspan,
                    name: first,
                    val: val.clone(),
                };
            }
            // All members are nested — recurse with `base.first` as the source.
            let nested_base = base.as_ref().map(|b| {
                SurfaceExpr::Proj(gspan, Box::new(b.clone()), Projection::Named(first.clone()))
            });
            let nested = build_nested_struct_lit(nested_base, members, None, span);
            SurfaceFieldAssign {
                span: gspan,
                name: first,
                val: nested,
            }
        })
        .collect();

    SurfaceExpr::StructLit {
        span,
        struct_type,
        base: base.map(Box::new),
        fields: assigns,
    }
}
