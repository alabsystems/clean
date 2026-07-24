// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Do notation parsing.
//! Extracted from expr.rs as part of #307.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse do notation: `do { elem1; elem2; ... }` or `do elem1; elem2; ...`
    ///
    /// Supports:
    /// - `let x := e` (pure let binding)
    /// - `let x <- e` / `let x ← e` (monadic bind)
    /// - `let mut x := e` (mutable binding, treated as let for now)
    /// - `return e` (early return, desugars to `Pure.pure e`)
    /// - `e` (expression statement; last one is the block result)
    ///
    /// Elements are separated by `;` or newlines (detected via block termination).
    pub(super) fn do_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Optional braces: `do { ... }` or `do ...`
        let braced = self.eat(&TokenKind::LBrace);

        // For unbraced `do`, push the first element's column as the reference.
        // Braced forms use bracket matching, so no indent tracking needed.
        if !braced {
            let first_elem_col = self.current().col;
            self.push_indent_for(first_elem_col, "do block");
        }

        let result = (|| {
            let mut elems = Vec::new();

            loop {
                // Check for end of do block
                if braced {
                    if self.eat(&TokenKind::RBrace) {
                        break;
                    }
                } else if self.at_do_elem_end() {
                    break;
                }

                let elem_span = self.current_span();
                let elem = self.parse_do_elem(elem_span)?;
                elems.push(elem);

                // Consume optional semicolons between elements
                while self.eat(&TokenKind::Semicolon) {}
            }

            if elems.is_empty() {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current().col as usize,
                    message: "empty do block".into(),
                });
            }

            let end_span = elems.last().map_or(start_span, |e| e.span());
            Ok(SurfaceExpr::Do(start_span.merge(end_span), elems))
        })();

        if !braced {
            if let Err(err) = &result {
                // Mirror `by_body`: record the recovery diagnostic while the
                // do block's indent context is still live, after advancing the
                // cursor to the nearest recovery boundary. This guarantees the
                // diagnostic's `recovered_at` points at the next top-level
                // declaration (a dedented decl keyword) rather than EOF — the
                // file-level `skip_to_next_decl` recovery would otherwise
                // over-consume the following declaration before flushing the
                // deferred diagnostic.
                self.defer_parser_recovery("do block", err);
                self.skip_to_do_recovery_boundary();
                self.flush_pending_parser_recoveries();
            }
            self.pop_indent();
        }

        result
    }

    /// Advance the cursor to the nearest do-block recovery boundary.
    ///
    /// Stops at the next top-level declaration keyword that has dedented out
    /// of the enclosing do block, at any dedent below the do block's reference
    /// column, or at EOF. Bounded brackets are tracked so a stray closer does
    /// not terminate recovery prematurely. This leaves the cursor on the
    /// boundary token so that a following declaration is still parsed as its
    /// own `RawDecl`/decl rather than being swallowed by error recovery.
    fn skip_to_do_recovery_boundary(&mut self) {
        // The do block's reference column was just pushed by `do_body`.
        let block_col = self.indent_stack.last().copied().unwrap_or(0);
        let mut depth: usize = 0;
        loop {
            if matches!(self.current_kind(), TokenKind::Eof) {
                break;
            }
            if depth == 0 {
                let tok = self.current();
                // A new-line token at a column below the do block's reference
                // ends the block; if it also starts a declaration we have
                // reached the next top-level boundary. Either way, stop here so
                // the boundary token is preserved for outer parsing.
                if tok.preceded_by_newline && tok.col < block_col {
                    break;
                }
            }
            match self.current_kind() {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth > 0 {
                        depth -= 1;
                    } else {
                        // Unbalanced closer: stop rather than escape the block.
                        break;
                    }
                }
                _ => {}
            }
            self.advance();
        }
    }

    /// Parse a single do-block element.
    pub(super) fn parse_do_elem(&mut self, elem_span: Span) -> Result<DoElem, ParseError> {
        match self.current_kind().clone() {
            TokenKind::Let => {
                self.advance();
                self.parse_do_let(elem_span)
            }
            TokenKind::Have => {
                self.advance();
                self.parse_do_have(elem_span)
            }
            TokenKind::Return => {
                self.advance();
                let val = self.parse_do_elem_expr()?;
                let span = elem_span.merge(val.span());
                Ok(DoElem::Return(span, Box::new(val)))
            }
            TokenKind::If => {
                self.advance();
                self.parse_do_if(elem_span)
            }
            TokenKind::Match => {
                self.advance();
                self.parse_do_match(elem_span)
            }
            TokenKind::Ident(ref s) => self.parse_do_ident_elem(s.clone(), elem_span),
            _ => self.parse_do_expr_or_bind(elem_span),
        }
    }

    /// Dispatch identifier-keyword do-elements (for, try, unless, while, etc.)
    fn parse_do_ident_elem(&mut self, kw: String, elem_span: Span) -> Result<DoElem, ParseError> {
        match kw.as_str() {
            "for" => {
                self.advance();
                self.parse_do_for(elem_span)
            }
            "try" => {
                self.advance();
                self.parse_do_try(elem_span)
            }
            "unless" => {
                self.advance();
                self.parse_do_unless(elem_span)
            }
            "when" => {
                self.advance();
                self.parse_do_when(elem_span)
            }
            "repeat" => {
                self.advance();
                self.parse_do_repeat(elem_span)
            }
            "while" => {
                self.advance();
                self.parse_do_while(elem_span)
            }
            "dbg_trace" => {
                self.advance();
                self.parse_do_dbg_trace(elem_span)
            }
            "assert!" => {
                self.advance();
                self.parse_do_assert(elem_span, "assert!")
            }
            "debug_assert!" => {
                self.advance();
                self.parse_do_assert(elem_span, "debug_assert!")
            }
            "match_expr" => {
                self.advance();
                self.parse_do_match_expr(elem_span)
            }
            "let_expr" => {
                self.advance();
                self.parse_do_let_expr(elem_span)
            }
            "break" => {
                self.advance();
                Ok(DoElem::Break(elem_span))
            }
            "continue" => {
                self.advance();
                Ok(DoElem::Continue(elem_span))
            }
            _ => self.parse_do_expr_or_bind(elem_span),
        }
    }

    /// Parse a do-block `let` element.
    ///
    /// Handles:
    /// - `let x := e` (pure let binding)
    /// - `let x <- e` / `let x ← e` (monadic bind)
    /// - `let mut x := e` (mutable let)
    /// - `let pat <- e | fallback` (refutable monadic bind)
    ///
    /// For refutable patterns (`.some x`, `Ctor args`, etc.), saves position
    /// and tries pattern parsing first. Falls back to identifier parsing on
    /// failure.
    fn parse_do_let(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        if self.eat(&TokenKind::Rec) {
            return self.parse_do_let_rec(start_span);
        }

        // Check for `mut` keyword (parsed as an identifier)
        let is_mut = matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "mut");
        if is_mut {
            self.advance();
        }

        // Try refutable pattern form first
        if !is_mut {
            if let Some(result) = self.try_parse_do_let_refutable(start_span)? {
                return Ok(result);
            }
        }

        // Irrefutable destructuring let: `let (a, b) := e` / `let ⟨a, b⟩ := e`.
        // Lean 4's `letPatDecl` (src/Lean/Parser/Do.lean) accepts a single-
        // constructor (tuple / anonymous-constructor / structure) pattern with no
        // `| fallback`, since it cannot fail. The refutable path above only fires
        // on constructor-application / `.ctor` starts and demands a fallback, so a
        // bare `(a, b)` / `⟨a, b⟩` previously fell through to `parse_do_let_binder`
        // and hard-failed on the `(` / `⟨`. We desugar exactly as Lean does:
        // `let pat := e; rest`  ≡  `match e with | pat => rest`, consuming the
        // remaining do-sequence as the single (irrefutable) arm body.
        if !is_mut {
            if let Some(result) = self.try_parse_do_let_irrefutable_pattern(start_span)? {
                return Ok(result);
            }
        }

        let binder = self.parse_do_let_binder()?;

        // Check for `<-` / `←` (monadic bind) vs `:=` (pure let)
        if self.eat(&TokenKind::LeftArrow) {
            let val = self.parse_do_elem_expr()?;

            // Check for refutable bind with simple identifier: `let x <- e | fallback`
            if !is_mut && self.eat(&TokenKind::Pipe) {
                let pat = SurfacePattern::Var(binder.name.clone());
                return self.parse_do_let_else(start_span, pat, val);
            }

            let span = start_span.merge(val.span());
            if is_mut {
                // `let mut x <- e` — treat as bind (mutable lifting deferred)
                Ok(DoElem::Bind(span, binder, Box::new(val)))
            } else {
                Ok(DoElem::Bind(span, binder, Box::new(val)))
            }
        } else if self.eat(&TokenKind::ColonEq) {
            let val = self.parse_do_elem_expr()?;
            let span = start_span.merge(val.span());
            if is_mut {
                Ok(DoElem::LetMut(span, binder, Box::new(val)))
            } else {
                Ok(DoElem::Let(span, binder, Box::new(val)))
            }
        } else {
            Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `:=` or `←`/`<-` in do let binding, got {:?}",
                    self.current_kind()
                ),
            })
        }
    }

    /// Try to parse an irrefutable destructuring `let pat := e` inside a do
    /// block, where `pat` is a single-constructor tuple `(a, b)` or anonymous
    /// constructor `⟨a, b⟩` pattern (no `| fallback`).
    ///
    /// Returns `Some(DoElem::Match)` desugaring `let pat := e; rest` to
    /// `match e with | pat => rest` (the remaining do-sequence becomes the
    /// single arm body), or `None` if the position does not start such a
    /// pattern (the caller then falls back to the simple-binder path). The
    /// parser position is restored on any non-match so existing forms are
    /// untouched.
    ///
    /// Only `(` / `⟨` starts are handled here; constructor-application and
    /// `.ctor` refutable patterns are routed through `try_parse_do_let_refutable`
    /// (which requires a fallback), exactly mirroring Lean 4's split between
    /// `letPatDecl` and `doPatDecl`.
    fn try_parse_do_let_irrefutable_pattern(
        &mut self,
        start_span: Span,
    ) -> Result<Option<DoElem>, ParseError> {
        if !matches!(self.current_kind(), TokenKind::LParen | TokenKind::LAngle) {
            return Ok(None);
        }

        let saved_pos = self.pos;
        let Ok(pat) = self.pattern() else {
            self.pos = saved_pos;
            return Ok(None);
        };

        // A `(`/`⟨` pattern parses to a right-nested `Prod.mk` (tuple /
        // anonymous-constructor) or `Unit.unit` (`()` / `⟨⟩`) `Ctor`; a bare
        // `(x)` parses to the inner pattern (e.g. `Var("x")`), which is not a
        // destructuring and belongs to the simple-binder path. We accept ONLY the
        // irrefutable single-constructor tuple/unit shapes here so refutable
        // parenthesized constructor patterns (e.g. `(Nat.succ n)`) still flow to
        // the fallback-requiring refutable path rather than silently losing their
        // exhaustiveness obligation.
        let is_irrefutable_destructuring = matches!(
            &pat,
            SurfacePattern::Ctor(head, _)
                if matches!(
                    head.as_str(),
                    "Prod.mk" | "PProd.mk" | "MProd.mk" | "Unit.unit"
                )
        );
        if !is_irrefutable_destructuring {
            self.pos = saved_pos;
            return Ok(None);
        }

        // Two irrefutable forms: pure `:=` and monadic `←`/`<-`.
        let is_monadic = if self.eat(&TokenKind::ColonEq) {
            false
        } else if self.eat(&TokenKind::LeftArrow) {
            true
        } else {
            self.pos = saved_pos;
            return Ok(None);
        };

        let value = self.parse_do_elem_expr()?;

        // A `| fallback` here means the user wrote a refutable destructuring with
        // an explicit else; defer to the refutable machinery for that shape.
        if matches!(self.current_kind(), TokenKind::Pipe) {
            self.eat(&TokenKind::Pipe);
            return self.parse_do_let_else(start_span, pat, value).map(Some);
        }

        // Consume the remaining do-sequence as the single (irrefutable) arm body.
        // Skip the optional element separators (`;`) so the continuation's first
        // statement leads the arm body (the outer `parse_do_seq` loop normally
        // eats these between siblings; here we consume them before recursing so
        // the nested `parse_do_seq` is not handed a bare separator and report an
        // empty branch).
        while self.eat(&TokenKind::Semicolon) {}
        let arm_span = self.current_span();
        let body = self.parse_do_seq()?;
        let end = body.last().map_or(arm_span, |e| e.span());
        let arm = DoMatchArm {
            span: arm_span.merge(end),
            patterns: vec![pat],
            body,
        };
        let span = start_span.merge(end);

        if is_monadic {
            // `let pat ← value; rest`  ≡  `value >>= fun __x => match __x with | pat => rest`.
            // Bind the monadic `value` to a fresh variable, then match that
            // variable against the irrefutable destructuring pattern — exactly
            // Lean 4's `doPatBind` desugaring.  Expressed as a nested two-element
            // do-block so the existing `DoElem::Bind` + `DoElem::Match`
            // desugaring handles the monad plumbing unchanged.
            let fresh = format!("__do_pat_{}", span.start);
            let fresh_binder = SurfaceBinder::new(fresh.clone(), None, SurfaceBinderInfo::Explicit);
            let scrut = SurfaceExpr::Ident(span, fresh);
            let bind_elem = DoElem::Bind(span, fresh_binder, Box::new(value));
            let match_elem = DoElem::Match(span, vec![scrut], vec![arm]);
            return Ok(Some(DoElem::Expr(
                span,
                Box::new(SurfaceExpr::Do(span, vec![bind_elem, match_elem])),
            )));
        }

        // `let pat := value; rest`  ≡  `match value with | pat => rest`.
        Ok(Some(DoElem::Match(span, vec![value], vec![arm])))
    }

    /// Parse `if ...` within a do block. Handles three forms:
    ///
    /// 1. `if let pat := scrutinee then doSeq else doSeq` (pattern matching)
    /// 2. `if h : prop then doSeq else doSeq` (decidable if with proof witness)
    /// 3. `if cond then doSeq else doSeq` (plain conditional)
    ///
    /// In Lean 4, `if` in do blocks has branches that are do-element sequences,
    /// not single expressions. This allows:
    ///   do if x > 0 then
    ///        let y <- f x
    ///        return y
    ///      else
    ///        return 0
    fn parse_do_if(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Form 1: `if let pat := scrutinee then doSeq else doSeq`
        if self.eat(&TokenKind::Let) {
            let pat = self.pattern_with_or()?;
            self.expect(&TokenKind::ColonEq)?;
            let scrutinee = self.expr()?;
            self.expect(&TokenKind::Then)?;
            let then_branch = self.parse_do_seq()?;
            let else_branch = if self.eat(&TokenKind::Else) {
                Some(self.parse_do_if_else_branch()?)
            } else {
                None
            };
            let end_span = self.do_if_end_span(&then_branch, &else_branch, start_span);
            return Ok(DoElem::IfLet(
                start_span.merge(end_span),
                pat,
                Box::new(scrutinee),
                then_branch,
                else_branch,
            ));
        }

        // Form 2: `if h : prop then doSeq else doSeq`
        // Check for `ident :` (not `:=`) pattern
        if let TokenKind::Ident(name) = self.current_kind() {
            if matches!(self.peek_kind(1), Some(TokenKind::Colon)) {
                let name = name.clone();
                self.advance(); // consume ident
                self.advance(); // consume :
                let prop = self.expr()?;
                self.expect(&TokenKind::Then)?;
                let then_branch = self.parse_do_seq()?;
                let else_branch = if self.eat(&TokenKind::Else) {
                    Some(self.parse_do_if_else_branch()?)
                } else {
                    None
                };
                let end_span = self.do_if_end_span(&then_branch, &else_branch, start_span);
                return Ok(DoElem::IfDecidable(
                    start_span.merge(end_span),
                    name,
                    Box::new(prop),
                    then_branch,
                    else_branch,
                ));
            }
        }

        // Form 3: plain `if cond then doSeq else doSeq`
        let cond = self.expr()?;
        self.expect(&TokenKind::Then)?;
        let (then_branch, else_branch) = self.parse_do_if_then_else()?;
        let end_span = self.do_if_end_span(&then_branch, &else_branch, start_span);
        Ok(DoElem::If(
            start_span.merge(end_span),
            Box::new(cond),
            then_branch,
            else_branch,
        ))
    }

    /// Parse `then doSeq (else doSeq)?` — the branch doSeq is greedy and
    /// indentation-delimited (`parse_do_seq` pushes the branch's first-element
    /// column; a sibling statement at the `if`'s shallower column dedents out),
    /// exactly Lean's `doIf` grammar: an else-less `then` owns EVERY statement
    /// indented past it. A former backtrack here truncated a multi-statement
    /// else-less branch to its first element, silently promoting the rest to
    /// unconditional siblings (wrong VALUES: `if c then a; b` ran `b` even when
    /// `c` was false) — and its indent-stack restore dropped the branch column,
    /// so a same-column `break` after a reassignment was swallowed into the
    /// application spine (`composite := (true break)`). B94.
    /// One exception, pinned by `test_do_if_no_else`: when the greedy branch
    /// was joined by an explicit same-line `;` (`{ if x then return 1;
    /// return 0 }`) and no `else` follows, the historical single-element
    /// truncation is kept — the `;` reads as returning to the enclosing
    /// sequence. Whether real Lean agrees for that exact shape is unverified
    /// (recorded); the indentation-joined case above is the unambiguous one.
    fn parse_do_if_then_else(&mut self) -> Result<(Vec<DoElem>, Option<Vec<DoElem>>), ParseError> {
        let saved_pos = self.pos;
        let saved_indent = self.indent_stack.clone();
        let (then_seq, semi_joined) = self.parse_do_seq_tracking_semis()?;
        if self.eat(&TokenKind::Else) {
            let else_branch = self.parse_do_if_else_branch()?;
            Ok((then_seq, Some(else_branch)))
        } else if then_seq.len() > 1 && semi_joined {
            // Same-line `;`-joined branch without `else`: keep the historical
            // first-element-only reading; the rest returns to the outer seq.
            self.pos = saved_pos;
            self.indent_stack = saved_indent;
            let elem_span = self.current_span();
            let single_elem = self.parse_do_elem(elem_span)?;
            Ok((vec![single_elem], None))
        } else {
            Ok((then_seq, None))
        }
    }

    /// Parse the else branch of a do-if, handling `else if` chaining.
    fn parse_do_if_else_branch(&mut self) -> Result<Vec<DoElem>, ParseError> {
        if matches!(self.current_kind(), TokenKind::If) {
            let if_span = self.current_span();
            self.advance();
            let nested_if = self.parse_do_if(if_span)?;
            Ok(vec![nested_if])
        } else {
            self.parse_do_seq()
        }
    }

    /// Compute the end span for a do-if element.
    fn do_if_end_span(
        &self,
        then_branch: &[DoElem],
        else_branch: &Option<Vec<DoElem>>,
        fallback: Span,
    ) -> Span {
        else_branch
            .as_ref()
            .and_then(|b| b.last())
            .map_or(then_branch.last().map_or(fallback, |e| e.span()), |e| {
                e.span()
            })
    }

    /// Parse `for x in xs do doSeq` within a do block.
    ///
    /// Lean 4 desugars this to `ForIn.forIn xs init (fun x acc => ...)`.
    /// We capture it as a first-class do element for proper desugaring.
    fn parse_do_for(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Parse binding variable
        let name = match self.current_kind() {
            TokenKind::Ident(_) => self.ident()?,
            TokenKind::Underscore => {
                self.advance();
                "_".to_string()
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!(
                        "expected identifier in for loop, got {:?}",
                        self.current_kind()
                    ),
                })
            }
        };

        // Expect `in` — may be lexed as keyword or identifier
        if self.eat(&TokenKind::In) {
            // ok - `in` was a keyword token
        } else if matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "in") {
            self.advance();
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected `in` in for loop, got {:?}", self.current_kind()),
            });
        }

        // Parse the collection expression (stop before `do` keyword).
        // Set forbid_do so that `do` is not consumed as a term prefix. (#1808)
        let saved_forbid_do = self.forbid_do;
        let saved_stop_at_newline_outer_indent = self.stop_app_at_newline_outer_indent;
        self.forbid_do = true;
        self.stop_app_at_newline_outer_indent = true;
        let collection = self.expr();
        self.stop_app_at_newline_outer_indent = saved_stop_at_newline_outer_indent;
        self.forbid_do = saved_forbid_do;
        let collection = collection?;

        // Expect `do` keyword
        if !self.eat(&TokenKind::Do) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected `do` in for loop, got {:?}", self.current_kind()),
            });
        }

        let body = self.parse_do_seq()?;
        let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
        let end_span = body.last().map_or(start_span, |e| e.span());
        Ok(DoElem::For(
            start_span.merge(end_span),
            binder,
            Box::new(collection),
            body,
        ))
    }

    /// Parse `match discrs with | pat => doSeq` within a do block.
    ///
    /// Match arms in a do block have do-element sequences as bodies,
    /// allowing monadic operations in each arm.
    fn parse_do_match(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Parse discriminees
        let mut discrs = vec![self.expr()?];
        while self.eat(&TokenKind::Comma) {
            discrs.push(self.expr()?);
        }
        self.expect(&TokenKind::With)?;

        // Column of this match's first arm `|`. A later `|` that begins a new
        // line at a *smaller* column belongs to an enclosing match and must
        // terminate this one — otherwise a nested do-match in an arm body
        // greedily swallows the outer match's subsequent arms (the
        // `getAllocIdFromPtrARC` shape in trust-ir's `Semantics/ARC.lean`,
        // and the Borrow/Aggregate/Memory siblings: the `.ptr` arm's inner
        // `match … find?` ate `| .nullPtr` / `| _`). A same-line `|`, or one
        // indented at least as far as the first arm, continues this match.
        // Mirrors the expression-level `match_body` guard (Track R) and
        // Lean 4 column-sensitive `matchAlts`.
        let arm_col = self.current().col;

        // Parse match arms with do-sequence bodies
        let mut arms = Vec::new();
        while self.check(&TokenKind::Pipe)
            && !(self.current().preceded_by_newline && self.current().col < arm_col)
        {
            self.advance(); // consume the `|`
            let arm_span = self.current_span();
            let mut patterns = vec![self.pattern_with_or()?];
            while self.eat(&TokenKind::Comma) {
                patterns.push(self.pattern_with_or()?);
            }
            self.expect(&TokenKind::FatArrow)?;
            let body = self.parse_do_seq()?;
            let end = body.last().map_or(arm_span, |e| e.span());
            arms.push(DoMatchArm {
                span: arm_span.merge(end),
                patterns,
                body,
            });
        }

        let end_span = arms
            .last()
            .and_then(|a| a.body.last())
            .map_or(start_span, |e| e.span());
        Ok(DoElem::Match(start_span.merge(end_span), discrs, arms))
    }
    /// Check if we're at the end of a do-block element sequence (unbraced mode).
    /// Similar to `at_tactic_end` but also stops at certain do-level boundaries.
    pub(super) fn at_do_elem_end(&self) -> bool {
        self.at_tactic_end(0)
    }
}
