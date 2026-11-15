// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0's testing and audit commands: `#guard e`, `#print axioms c` and
//! `/-- expected -/ #guard_msgs (spec)? in cmd`; and Lean 4.30.0-rc2's
//! `#reduce (proofs := true)? (types := true)? e`.
//!
//! Before these existed every one of them fell into `hash_command`'s
//! unknown-command arm, which skipped to the next command and returned a
//! `#check _`: the hole elaborated to a metavariable, the metavariable reached
//! the kernel as an unknown free variable, and the command failed with
//! `Kernel check failed for [anonymous]`. For `#guard_msgs in #print axioms c`
//! the skip stopped at `#print`, which read `axioms` as the constant to print
//! and left `c` behind as an unknown command — three failures for one gate,
//! none of which said what the gate checks. That arm no longer fabricates a
//! command: an unknown `#cmd` is a `RawDecl` naming it.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// `#print axioms c`, entered with `#print` consumed and `axioms` current.
    ///
    /// Lean's `printAxioms` is `"#print " >> nonReservedSymbol "axioms " >>
    /// ident` beside `print := "#print " >> (ident <|> strLit)`; the longest
    /// parse wins, so `axioms` is the keyword exactly when an identifier
    /// follows it. The caller checks that.
    pub(in crate::grammar) fn print_axioms_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        self.advance(); // `axioms`
        let name = self.qualified_ident()?;
        Ok(SurfaceDecl::PrintAxioms {
            span: start_span,
            name,
        })
    }

    /// Whether the current token is the `axioms` of `#print axioms c`.
    pub(in crate::grammar) fn at_print_axioms_keyword(&self) -> bool {
        let current = self.current();
        matches!(&current.kind, TokenKind::Ident(word) if word == "axioms")
            && !current.ident_escaped
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
    }

    /// `#reduce (proofs := true)? (types := true)? e`, entered with
    /// `#reduce` consumed.
    ///
    /// Lean 4.30.0-rc2's `reduceCmd` is `"#reduce " >> (atomic("(" &"proofs"
    /// " := " &"true" ")"))? >> (atomic("(" &"types" " := " &"true" ")"))? >>
    /// term`: each group is optional, `proofs` comes before `types`, and only
    /// the literal `true` is accepted.
    pub(in crate::grammar) fn reduce_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let reduce_proofs = self.eat_reduce_flag("proofs");
        let reduce_types = self.eat_reduce_flag("types");
        // Anything else of the shape `(x := …)` here is no flag and no term:
        // pinned Lean fails with `unexpected token ':='; expected ')', ',' or
        // ':'` (measured on `#reduce (proofs := false) 1` and on the flags out
        // of order). The expression parser would read it as a named argument,
        // which the elaborator takes as its bare value.
        if matches!(self.peek_kind(0), Some(TokenKind::LParen))
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
            && matches!(self.peek_kind(2), Some(TokenKind::ColonEq))
        {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "unexpected token ':='; expected ')', ',' or ':'".to_owned(),
            });
        }
        let expr = self.expr()?;
        Ok(SurfaceDecl::Reduce {
            span: start_span,
            expr: Box::new(expr),
            reduce_proofs,
            reduce_types,
        })
    }

    /// Consume `( <word> := true )` when it is next, as one atomic group.
    fn eat_reduce_flag(&mut self, word: &str) -> bool {
        let keyword_at = |offset: usize, expected: &str| {
            self.peek_token(offset).is_some_and(|token| {
                !token.ident_escaped
                    && matches!(&token.kind, TokenKind::Ident(found) if found == expected)
            })
        };
        let is_flag = matches!(self.peek_kind(0), Some(TokenKind::LParen))
            && keyword_at(1, word)
            && matches!(self.peek_kind(2), Some(TokenKind::ColonEq))
            && keyword_at(3, "true")
            && matches!(self.peek_kind(4), Some(TokenKind::RParen));
        if is_flag {
            for _ in 0..5 {
                self.advance();
            }
        }
        is_flag
    }

    /// `#guard e`, entered with `#guard` consumed.
    pub(in crate::grammar) fn guard_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let expr = self.expr()?;
        Ok(SurfaceDecl::Guard {
            span: start_span,
            expr: Box::new(expr),
        })
    }

    /// `#guard_msgs (spec)? in cmd`, entered with `#guard_msgs` consumed.
    /// `hash_index` is the token index of its `#`: the expectation is the doc
    /// comment written immediately before that token (Lean's grammar is
    /// `(docComment)? "#guard_msgs" …`).
    pub(in crate::grammar) fn guard_msgs_decl(
        &mut self,
        start_span: Span,
        hash_index: usize,
    ) -> Result<SurfaceDecl, ParseError> {
        let doc = self.doc_text_immediately_before(hash_index);
        let spec = if self.check(&TokenKind::LParen) {
            self.guard_msgs_spec()?
        } else {
            Vec::new()
        };
        if !self.eat(&TokenKind::In) {
            return Err(self.guard_msgs_error("expected `in` after `#guard_msgs`"));
        }
        let cmd = self.decl()?;
        Ok(SurfaceDecl::GuardMsgs {
            span: start_span,
            doc,
            spec,
            cmd: Box::new(cmd),
        })
    }

    /// The text between `/--` and `-/` of the doc comment that ends before
    /// token `index` with no token between them — Lean's `getDocStringText`
    /// (the raw text; `#guard_msgs` trims it itself).
    fn doc_text_immediately_before(&self, index: usize) -> Option<String> {
        let target = self.tokens.get(index)?;
        let previous_end = index
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or(0, |t| t.span.end);
        let doc = self
            .doc_comments
            .iter()
            .rev()
            .find(|d| d.span.end <= target.span.start)?;
        if doc.span.start < previous_end {
            return None;
        }
        let raw = self.source.get(doc.span.start..doc.span.end)?;
        let inner = raw.strip_prefix("/--")?.strip_suffix("-/")?;
        Some(inner.to_owned())
    }

    /// `"(" guardMsgsSpecElt,* ")"`.
    fn guard_msgs_spec(&mut self) -> Result<Vec<GuardMsgsSpecElt>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut elts = Vec::new();
        if self.eat(&TokenKind::RParen) {
            return Ok(elts);
        }
        loop {
            elts.push(self.guard_msgs_spec_elt()?);
            if self.eat(&TokenKind::Comma) {
                continue;
            }
            self.expect(&TokenKind::RParen)?;
            return Ok(elts);
        }
    }

    /// `guardMsgsFilter <|> guardMsgsWhitespace <|> guardMsgsOrdering`.
    fn guard_msgs_spec_elt(&mut self) -> Result<GuardMsgsSpecElt, ParseError> {
        let word = self.guard_msgs_word()?;
        match word.as_str() {
            "whitespace" => {
                self.expect(&TokenKind::ColonEq)?;
                let mode = match self.guard_msgs_word()?.as_str() {
                    "exact" => GuardMsgsWhitespace::Exact,
                    "normalized" => GuardMsgsWhitespace::Normalized,
                    "lax" => GuardMsgsWhitespace::Lax,
                    _ => {
                        return Err(self.guard_msgs_error(
                            "expected `exact`, `normalized` or `lax` after `whitespace :=`",
                        ))
                    }
                };
                Ok(GuardMsgsSpecElt::Whitespace(mode))
            }
            "ordering" => {
                self.expect(&TokenKind::ColonEq)?;
                let mode = match self.guard_msgs_word()?.as_str() {
                    "exact" => GuardMsgsOrdering::Exact,
                    "sorted" => GuardMsgsOrdering::Sorted,
                    _ => {
                        return Err(self
                            .guard_msgs_error("expected `exact` or `sorted` after `ordering :=`"))
                    }
                };
                Ok(GuardMsgsSpecElt::Ordering(mode))
            }
            "drop" => {
                let severity = self.guard_msgs_severity()?;
                Ok(GuardMsgsSpecElt::Filter {
                    drop: true,
                    severity,
                })
            }
            other => match guard_msgs_severity_word(other) {
                Some(severity) => Ok(GuardMsgsSpecElt::Filter {
                    drop: false,
                    severity,
                }),
                None => Err(self.guard_msgs_error(
                    "expected a `#guard_msgs` clause: `info`, `warning`, `error`, `all`, \
                     `drop …`, `whitespace := …` or `ordering := …`",
                )),
            },
        }
    }

    fn guard_msgs_severity(&mut self) -> Result<GuardMsgsSeverity, ParseError> {
        let word = self.guard_msgs_word()?;
        guard_msgs_severity_word(&word).ok_or_else(|| {
            self.guard_msgs_error("expected `info`, `warning`, `error` or `all` after `drop`")
        })
    }

    /// One non-reserved word of the spec grammar (Lean's `&"…"` symbols match
    /// an unescaped identifier spelled so).
    fn guard_msgs_word(&mut self) -> Result<String, ParseError> {
        let current = self.current();
        match &current.kind {
            TokenKind::Ident(word) if !current.ident_escaped => {
                let word = word.clone();
                self.advance();
                Ok(word)
            }
            _ => Err(self.guard_msgs_error("expected a `#guard_msgs` configuration word")),
        }
    }

    fn guard_msgs_error(&self, message: &str) -> ParseError {
        ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current().col as usize,
            message: format!("{message}, got {:?}", self.current_kind()),
        }
    }
}

fn guard_msgs_severity_word(word: &str) -> Option<GuardMsgsSeverity> {
    match word {
        "info" => Some(GuardMsgsSeverity::Info),
        "warning" => Some(GuardMsgsSeverity::Warning),
        "error" => Some(GuardMsgsSeverity::Error),
        "all" => Some(GuardMsgsSeverity::All),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::*;

    fn parse(source: &str) -> Vec<SurfaceDecl> {
        crate::parse_file(source).unwrap_or_else(|e| panic!("parse error: {e}\n{source}"))
    }

    #[test]
    fn test_parse_guard_msgs_reads_doc_spec_and_command() {
        let decls = parse(
            "/-- info: 'c' depends on axioms: [propext] -/\n\
             #guard_msgs (error, drop all, whitespace := lax, ordering := sorted) in\n\
             #print axioms Foo.c\n",
        );
        let [SurfaceDecl::GuardMsgs { doc, spec, cmd, .. }] = decls.as_slice() else {
            panic!("expected one #guard_msgs, got {decls:?}");
        };
        assert_eq!(
            doc.as_deref(),
            Some(" info: 'c' depends on axioms: [propext] ")
        );
        assert_eq!(
            spec.as_slice(),
            [
                GuardMsgsSpecElt::Filter {
                    drop: false,
                    severity: GuardMsgsSeverity::Error
                },
                GuardMsgsSpecElt::Filter {
                    drop: true,
                    severity: GuardMsgsSeverity::All
                },
                GuardMsgsSpecElt::Whitespace(GuardMsgsWhitespace::Lax),
                GuardMsgsSpecElt::Ordering(GuardMsgsOrdering::Sorted),
            ]
        );
        assert!(
            matches!(cmd.as_ref(), SurfaceDecl::PrintAxioms { name, .. } if name.to_string() == "Foo.c"),
            "{cmd:?}"
        );
    }

    #[test]
    fn test_parse_guard_msgs_doc_separated_by_a_token_is_not_its_expectation() {
        // The doc comment belongs to `def x`; `#guard_msgs` has none.
        let decls = parse("/-- doc of x -/\ndef x := 1\n#guard_msgs in\n#guard true\n");
        assert_eq!(decls.len(), 2, "{decls:?}");
        let SurfaceDecl::GuardMsgs { doc, cmd, .. } = &decls[1] else {
            panic!("expected #guard_msgs, got {:?}", decls[1]);
        };
        assert_eq!(doc, &None);
        assert!(matches!(cmd.as_ref(), SurfaceDecl::Guard { .. }), "{cmd:?}");
    }

    #[test]
    fn test_parse_axiom_audit_shape_one_command_per_gate() {
        // The `AxiomAudit.lean` shape: each gate is ONE command. Before, each
        // was three (`#check _`, `#print axioms`, and the constant left over
        // as an unknown command).
        let decls = parse(
            "namespace A\n\
             /-- info: 'A.t' does not depend on any axioms -/\n#guard_msgs in\n#print axioms t\n\
             /-- info: 'A.u' does not depend on any axioms -/\n#guard_msgs in\n#print axioms u\n\
             end A\n",
        );
        let [SurfaceDecl::Namespace { decls: inner, .. }] = decls.as_slice() else {
            panic!("{decls:?}");
        };
        assert_eq!(inner.len(), 2, "{inner:?}");
        assert!(inner
            .iter()
            .all(|d| matches!(d, SurfaceDecl::GuardMsgs { doc: Some(_), .. })));
    }

    #[test]
    fn test_parse_print_axioms_needs_a_following_identifier() {
        // `#print axioms` with no identifier after it is `#print` of the
        // constant `axioms`, as in Lean's longest match between the two.
        let decls = parse("#print axioms\n#guard true\n");
        assert!(
            matches!(&decls[0], SurfaceDecl::Print { name, .. } if name.to_string() == "axioms"),
            "{decls:?}"
        );
        assert!(matches!(&decls[1], SurfaceDecl::Guard { .. }), "{decls:?}");
    }

    #[test]
    fn test_parse_guard_term_continues_on_an_indented_line() {
        let decls = parse("#guard f (g 1)\n  (h 2) = true\n#guard true\n");
        assert_eq!(decls.len(), 2, "{decls:?}");
        assert!(decls.iter().all(|d| matches!(d, SurfaceDecl::Guard { .. })));
    }

    #[test]
    fn test_parse_guard_msgs_without_in_is_refused() {
        assert!(crate::parse_decl("#guard_msgs #print axioms t").is_err());
    }

    #[test]
    fn test_parse_unknown_hash_command_is_a_named_refusal() {
        // Lean 4.8.0 rejects an unknown command at parse time. Clean used to
        // skip it and substitute `#check _`; now it is a `RawDecl` that names
        // the command, and the next command still parses.
        let decls = parse("#frobnicate 1 (2 : Nat)\ntheorem t : True := True.intro\n");
        assert_eq!(decls.len(), 2, "{decls:?}");
        assert!(
            matches!(&decls[0], SurfaceDecl::RawDecl { content, .. }
                if content.starts_with("unknown command `#frobnicate`")),
            "{decls:?}"
        );
        assert!(
            matches!(&decls[1], SurfaceDecl::Theorem { .. }),
            "{decls:?}"
        );
    }
}
