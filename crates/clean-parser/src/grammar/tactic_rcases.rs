// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsers for Lean's recursive-cases family — `obtain`, `rcases`, `rintro` —
//! and the rcases pattern grammar they share (`Init/RCases.lean`):
//!
//! ```text
//! rcasesPat    := ident | "_" | "-" | "@" noWs rcasesPat
//!               | "⟨" rcasesPatLo,* "⟩" | "(" rcasesPatLo ")"     (and `rfl`, an ident)
//! rcasesPatMed := sepBy1(rcasesPat, " | ")
//! rcasesPatLo  := rcasesPatMed (" : " term)?
//! rintroPat    := rcasesPat | "(" rintroPat+ (" : " term)? ")"
//! ```
//!
//! A pattern is captured as canonical source text that the elaborator's
//! `RIntroPattern::parse` reads back; a written type `p : t` is kept as a term
//! in `rcases_pattern_types` and the text refers to it as `p : #k`.
//!
//! These are inherent methods on `Parser`, callable from the main tactic
//! dispatch in `tactic.rs`. Split from `tactic_sub.rs` (500-line limit).

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceExpr, SurfaceRCasesTarget, SurfaceTactic};
use crate::ParseError;

/// One pattern of an `rintro`, as captured: its canonical text and whether it
/// carries a type of its own. A binder group's type and the trailing
/// `rintro … : t` type the patterns that do not (`expandRIntroPat`,
/// `Lean/Elab/Tactic/RCases.lean`: the innermost type wins).
struct RintroItem {
    text: String,
    typed: bool,
}

/// Whether pattern text has one of `marks` outside every bracket.
/// Guillemet-escaped identifier text is skipped.
fn has_top_level(text: &str, marks: &[char]) -> bool {
    let mut depth = 0_i32;
    let mut escaped = false;
    for ch in text.chars() {
        match ch {
            '«' => escaped = true,
            '»' => escaped = false,
            _ if escaped => {}
            '⟨' | '(' | '[' => depth += 1,
            '⟩' | ')' | ']' => depth -= 1,
            _ if depth == 0 && marks.contains(&ch) => return true,
            _ => {}
        }
    }
    false
}

/// Whether pattern text is an alternation or typed (`|` or `:` outside every
/// bracket), so that it must be parenthesized to stand as one alternative of
/// an enclosing alternation.
fn is_compound_pattern(text: &str) -> bool {
    has_top_level(text, &['|', ':'])
}

impl RintroItem {
    /// An item for `text`, typed when the text already ends in its own `: #k`.
    fn new(text: String) -> Self {
        let typed = has_top_level(&text, &[':']);
        Self { text, typed }
    }
}

impl Parser {
    /// Whether the current token can begin an `rcasesPat` (or `rintroPat`).
    fn starts_rcases_pattern(&self) -> bool {
        matches!(
            self.current_kind(),
            TokenKind::LAngle
                | TokenKind::LParen
                | TokenKind::Underscore
                | TokenKind::Ident(_)
                | TokenKind::Rfl
                | TokenKind::Minus
                | TokenKind::At
        )
    }

    /// Record `ty` as the next pattern type and return its index `k`.
    fn push_rcases_pattern_type(&mut self) -> Result<usize, ParseError> {
        let ty = self.parse_tactic_expr()?;
        let index = self.rcases_pattern_types.len();
        self.rcases_pattern_types.push(ty);
        Ok(index)
    }

    /// Parse `obtain pat (: T)? := e` in tactic mode.
    ///
    /// The leading keyword (`obtain`) has already been consumed. Parses an
    /// optional destructuring pattern (`rcasesPatMed`), an optional `: T` type
    /// ascription, the `:=` separator, and the RHS scrutinee term. Mirrors
    /// [`Self::parse_tactic_have`] so the `:=` separator is handled directly
    /// rather than by the generic expr-list arg parser (which has no `:=`
    /// handling).
    ///
    /// The pattern is captured as its canonical source text so the elaborator
    /// can reuse the recursive-intro pattern engine (`RIntroPattern`) without
    /// the parser depending on `clean-elab` types.
    pub(crate) fn parse_tactic_obtain(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let outer_types = std::mem::take(&mut self.rcases_pattern_types);
        let result = self.parse_tactic_obtain_inner(start);
        let pattern_types = std::mem::replace(&mut self.rcases_pattern_types, outer_types);
        result.map(|tac| match tac {
            SurfaceTactic::Obtain {
                span,
                pattern,
                ty,
                term,
                ..
            } => SurfaceTactic::Obtain {
                span,
                pattern,
                ty,
                term,
                pattern_types,
                pattern_binders: Vec::new(),
            },
            other => other,
        })
    }

    fn parse_tactic_obtain_inner(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        // Optional pattern (`rcasesPatMed`, so a top-level `|` alternation is
        // included: `obtain hp | hq := h` splits an `Or`). When omitted
        // (`obtain : T := e`), default the binder to an anonymous `h` pattern.
        // A `:`/`:=` here means no leading pattern, which none of the pattern
        // start tokens can be.
        let pattern = if self.starts_rcases_pattern() {
            self.parse_rcases_pattern_with_alts()?
        } else {
            "h".to_string()
        };

        // Optional `: T` type ascription.
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.parse_tactic_expr()?))
        } else {
            None
        };

        // `(" := " term,+)?`, then the RHS scrutinee term. Without it,
        // `obtain pat : T` leaves `⊢ T` to prove (`obtainNone`), which needs
        // the type: with neither, `:=` is what is missing.
        let term = if ty.is_none() || self.check(&TokenKind::ColonEq) {
            self.expect(&TokenKind::ColonEq)?;
            Some(Box::new(self.parse_tactic_expr()?))
        } else {
            None
        };
        let end = term
            .as_deref()
            .or(ty.as_deref())
            .map_or(start, SurfaceExpr::span);

        Ok(SurfaceTactic::Obtain {
            span: start.merge(end),
            pattern,
            ty,
            term,
            pattern_types: Vec::new(),
            pattern_binders: Vec::new(),
        })
    }

    /// Parse an anonymous-constructor pattern `⟨p1, p2, ...⟩` (`rcasesPat.tuple`,
    /// `"⟨" rcasesPatLo,* "⟩"`) into its canonical `⟨...⟩` source text.
    ///
    /// The current token must be `⟨` (`TokenKind::LAngle`). Each field is a
    /// full `rcasesPatLo`, so an `Or`-alternation `p₁ | p₂` or a typed pattern
    /// may appear as a field (e.g. `⟨hp, hq | hr⟩`, destructuring `p ∧ (q ∨
    /// r)`): the field reader consumes the trailing `| ...` alternatives at the
    /// same bracket level, leaving the enclosing `,`/`⟩` for this loop.
    fn parse_obtain_anon_pattern(&mut self) -> Result<String, ParseError> {
        self.expect(&TokenKind::LAngle)?;
        let mut out = String::from("⟨");
        let mut first = true;
        while !self.check(&TokenKind::RAngle) {
            if !first {
                self.expect(&TokenKind::Comma)?;
                out.push_str(", ");
            }
            first = false;
            out.push_str(&self.parse_rcases_pattern_lo()?);
        }
        self.expect(&TokenKind::RAngle)?;
        out.push('⟩');
        Ok(out)
    }

    /// Parse `rcases casesTarget,* (with rcasesPatLo)?` in tactic mode
    /// (`Init/RCases.lean`), each `casesTarget := (ident " : ")? term`.
    ///
    /// Parsing stops cleanly at the pattern's end, leaving any `;`-sequenced
    /// continuation for the tactic sequencer. When no `with`-clause is
    /// present, the pattern is the empty tuple `⟨⟩`, as Lean's `evalRCases`
    /// makes it (`RCasesPatt.tuple tk []`): one target is split ONE level,
    /// every field `_`; several targets each take `_`.
    pub(crate) fn parse_tactic_rcases(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut targets = vec![self.parse_rcases_target()?];
        while self.eat(&TokenKind::Comma) {
            targets.push(self.parse_rcases_target()?);
        }
        let end = targets.last().map_or(start, |target| target.term.span());

        let outer_types = std::mem::take(&mut self.rcases_pattern_types);
        let pattern = if self.eat(&TokenKind::With) {
            // `" with " rcasesPatLo`: the top-level pattern may be typed.
            self.parse_rcases_pattern_lo()
        } else {
            Ok("⟨⟩".to_string())
        };
        let pattern_types = std::mem::replace(&mut self.rcases_pattern_types, outer_types);
        let pattern = pattern?;

        Ok(SurfaceTactic::RCases {
            span: start.merge(end),
            targets,
            pattern,
            pattern_types,
            pattern_binders: Vec::new(),
        })
    }

    /// One `casesTarget := (ident " : ")? term`. The prefix is an identifier
    /// IMMEDIATELY followed by `:`, and no term starts that way, so the
    /// two-token lookahead is exact (as for `cases h : e`). Without it the `:`
    /// ended the tactic and the proof fell to parser recovery.
    fn parse_rcases_target(&mut self) -> Result<SurfaceRCasesTarget, ParseError> {
        let eq_name = if matches!(self.current_kind(), TokenKind::Ident(_))
            && matches!(self.peek_kind(1), Some(TokenKind::Colon))
        {
            let name = self.expect_ident("rcases target equation name")?;
            self.expect(&TokenKind::Colon)?;
            Some(name)
        } else {
            None
        };
        let term = self.parse_tactic_expr()?;
        Ok(SurfaceRCasesTarget { eq_name, term })
    }

    /// `rcasesPatLo := rcasesPatMed (" : " term)?` (`Init/RCases.lean`): a
    /// pattern with its alternatives, then an optional type. The type is kept
    /// as a term in `rcases_pattern_types`, and the text refers to it as
    /// `pat : #k`, which `RIntroPattern::parse` reads back as a typed pattern.
    fn parse_rcases_pattern_lo(&mut self) -> Result<String, ParseError> {
        let pattern = self.parse_rcases_pattern_with_alts()?;
        if !self.eat(&TokenKind::Colon) {
            return Ok(pattern);
        }
        let index = self.push_rcases_pattern_type()?;
        Ok(format!("{pattern} : #{index}"))
    }

    /// `rcasesPatMed := sepBy1(rcasesPat, " | ")`: one leaf plus any trailing
    /// `|`-alternatives at the current bracket level.
    ///
    /// A `|` that begins a new line belongs to an enclosing construct (the
    /// `·`/`|` of a following focus block or `cases`/`induction` alt list) and
    /// ends the alternation — alternation `|`s in the `rcases`/`obtain`/
    /// `rintro` surface sit on the same line as the pattern.
    ///
    /// A leaf read from a parenthesized group drops its parens; one that is
    /// itself an alternation or typed (`(hp | hq) | hr`, `(h : t) | g`) gets
    /// them back here, so that the combined text still groups the way it was
    /// written (`rcasesPat.paren` resets the precedence to low).
    fn parse_rcases_pattern_with_alts(&mut self) -> Result<String, ParseError> {
        let mut alternatives = vec![self.parse_rcases_leaf_pattern()?];
        while matches!(self.current_kind(), TokenKind::Pipe) && !self.current().preceded_by_newline
        {
            self.advance(); // consume `|`
            alternatives.push(self.parse_rcases_leaf_pattern()?);
        }
        if alternatives.len() == 1 {
            return Ok(alternatives.swap_remove(0));
        }
        Ok(alternatives
            .into_iter()
            .map(|alt| {
                if is_compound_pattern(&alt) {
                    format!("({alt})")
                } else {
                    alt
                }
            })
            .collect::<Vec<_>>()
            .join(" | "))
    }

    /// Parse a single `rcasesPat` (no top-level `|` alternation).
    ///
    /// * `⟨...⟩` — a tuple ([`Self::parse_obtain_anon_pattern`]);
    /// * `( rcasesPatLo )` — a group, returned WITHOUT its parens (the inner
    ///   text is a complete pattern; `rintro (hp | hq)` reads `hp | hq`);
    /// * `_` — keep the component under an inaccessible name;
    /// * `-` — clear the component (`rcasesPat.clear`);
    /// * `@pat` — bind every constructor argument, implicit ones included
    ///   (`rcasesPat.explicit`, `"@" noWs rcasesPat`); a parenthesized `pat`
    ///   keeps its parens so the `@` applies to the whole group;
    /// * `rfl` — substitute the equation away (`rfl` is a keyword token here,
    ///   an identifier in Lean);
    /// * an identifier — name the component.
    fn parse_rcases_leaf_pattern(&mut self) -> Result<String, ParseError> {
        match self.current_kind() {
            TokenKind::LAngle => self.parse_obtain_anon_pattern(),
            TokenKind::LParen => {
                self.advance();
                let inner = self.parse_rcases_pattern_lo()?;
                self.expect(&TokenKind::RParen)?;
                Ok(inner)
            }
            TokenKind::Underscore => {
                self.advance();
                Ok("_".to_string())
            }
            TokenKind::Rfl => {
                self.advance();
                Ok("rfl".to_string())
            }
            TokenKind::Minus => {
                self.advance();
                Ok("-".to_string())
            }
            TokenKind::At => {
                let at_end = self.current_span().end;
                self.advance();
                if self.current_span().start != at_end {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: "expected a pattern immediately after `@` in an rcases pattern \
                                  (no whitespace)"
                            .to_string(),
                    });
                }
                let grouped = self.check(&TokenKind::LParen);
                let inner = self.parse_rcases_leaf_pattern()?;
                Ok(if grouped {
                    format!("@({inner})")
                } else {
                    format!("@{inner}")
                })
            }
            _ => self
                .expect_ident("rcases pattern")?
                .source_spelling()
                .ok_or_else(|| ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "pattern identifier has no source spelling".to_string(),
                }),
        }
    }

    /// Parse `rintro pat₁ pat₂ … (: t)?` in tactic mode.
    ///
    /// The leading keyword (`rintro`) has already been consumed. Parses one or
    /// more space-separated `rintroPat`s, each captured as canonical pattern
    /// text through the SAME readers `rcases`/`obtain` use. A binder group
    /// `(x y : t)` stands for one pattern per member, each typed `t`, and a
    /// trailing `: t` types every pattern that has no type of its own
    /// (`expandRIntroPats`, `Lean/Elab/Tactic/RCases.lean`).
    ///
    /// Capturing each pattern as text (rather than letting the generic
    /// expr-list arg parser elaborate `⟨...⟩` as a term-mode anonymous
    /// constructor) is what lets the elaborator route `rintro` through the
    /// kernel-checked `intro` + `destruct_named_hypothesis` engine instead of the
    /// stale-FVar term path.
    ///
    /// Patterns sit on the same source line as `rintro`; parsing stops at the
    /// first newline-preceded token (or `;`/end-of-block) so a `;`-sequenced
    /// continuation or the next line's tactic is never swallowed.
    pub(crate) fn parse_tactic_rintro(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let outer_types = std::mem::take(&mut self.rcases_pattern_types);
        let result = self.parse_tactic_rintro_inner(start);
        let pattern_types = std::mem::replace(&mut self.rcases_pattern_types, outer_types);
        result.map(|tac| match tac {
            SurfaceTactic::RIntro { span, patterns, .. } => SurfaceTactic::RIntro {
                span,
                patterns,
                pattern_types,
                pattern_binders: Vec::new(),
            },
            other => other,
        })
    }

    fn parse_tactic_rintro_inner(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut items = Vec::new();
        let mut last_span = start;

        while self.starts_rcases_pattern()
            && (items.is_empty() || !self.current().preceded_by_newline)
        {
            last_span = self.current().span;
            self.parse_rintro_pat(&mut items)?;
        }

        if items.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "rintro: expected at least one pattern".to_string(),
            });
        }

        // `(" : " term)?`: the type of every pattern that has none of its own.
        if self.check(&TokenKind::Colon) && !self.current().preceded_by_newline {
            self.advance();
            last_span = self.current().span;
            let index = self.push_rcases_pattern_type()?;
            ascribe_rintro_items(&mut items, index);
        }

        Ok(SurfaceTactic::RIntro {
            span: start.merge(last_span),
            patterns: items.into_iter().map(|item| item.text).collect(),
            pattern_types: Vec::new(),
            pattern_binders: Vec::new(),
        })
    }

    /// Parse one `rintroPat`, appending the patterns it stands for to `out`:
    /// an `rcasesPat` (with any same-line `|` alternatives, which `rintro`
    /// has always accepted), or the binder group `"(" rintroPat+ (" : " term)?
    /// ")"`. A group of one pattern is the parenthesized pattern itself
    /// (`(hp | hq)`, `(h : t)`).
    fn parse_rintro_pat(&mut self, out: &mut Vec<RintroItem>) -> Result<(), ParseError> {
        if !self.check(&TokenKind::LParen) {
            out.push(RintroItem::new(self.parse_rcases_pattern_with_alts()?));
            return Ok(());
        }
        self.advance(); // `(`
        let mut group = vec![RintroItem::new(self.parse_rcases_pattern_with_alts()?)];
        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Colon) {
            self.parse_rintro_pat(&mut group)?;
        }
        if self.eat(&TokenKind::Colon) {
            let index = self.push_rcases_pattern_type()?;
            ascribe_rintro_items(&mut group, index);
        }
        self.expect(&TokenKind::RParen)?;
        out.extend(group);
        Ok(())
    }
}

/// Give every untyped item the pattern type `#index`.
fn ascribe_rintro_items(items: &mut [RintroItem], index: usize) {
    for item in items.iter_mut().filter(|item| !item.typed) {
        item.text = format!("{} : #{index}", item.text);
        item.typed = true;
    }
}

#[cfg(test)]
mod tests {
    use super::is_compound_pattern;

    #[test]
    fn test_is_compound_pattern_reads_only_top_level_structure() {
        assert!(is_compound_pattern("hp | hq"));
        assert!(is_compound_pattern("h : #0"));
        assert!(!is_compound_pattern("⟨hp, hq | hr⟩"));
        assert!(!is_compound_pattern("@(a | b)"));
        assert!(!is_compound_pattern("«a|b»"));
        assert!(!is_compound_pattern("-"));
    }
}
