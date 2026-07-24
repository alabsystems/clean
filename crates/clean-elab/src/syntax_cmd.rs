// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Syntax declaration registry and lightweight token-level matching for Lean 5.

use std::collections::HashMap;

use clean_parser::lexer::{Token, TokenKind};
use clean_parser::{SurfaceExpr, SurfaceLit, SyntaxPatternItem};

/// Standard Lean syntax categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SyntaxCategory {
    Term,
    Tactic,
    Command,
    Doelem,
    Level,
}

impl SyntaxCategory {
    /// Return the canonical category name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Term => "term",
            Self::Tactic => "tactic",
            Self::Command => "command",
            Self::Doelem => "doElem",
            Self::Level => "level",
        }
    }
}

/// Captured result from matching a syntax pattern.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SyntaxMatch {
    Token(String),
    Expr(SurfaceExpr),
    Optional(Option<Box<SyntaxMatch>>),
    Repeat(Vec<SyntaxMatch>),
}

/// A registered syntax rule.
#[derive(Debug, Clone)]
pub struct SyntaxRule {
    pub name: String,
    pub category: SyntaxCategory,
    pub pattern: Vec<SyntaxPatternItem>,
    pub priority: u32,
}

/// Errors for syntax registration and matching.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum SyntaxError {
    #[error("unknown syntax category: {0}")]
    UnknownCategory(String),
    #[error("duplicate syntax rule: {name}")]
    DuplicateRule { name: String },
    #[error("syntax rule '{name}' has an empty pattern")]
    EmptyPattern { name: String },
    #[error("syntax match failed for {category}: {detail}")]
    MatchFailed { category: String, detail: String },
}

/// Priority-ordered syntax registry keyed by leading literal.
pub struct SyntaxRegistry {
    entries: HashMap<String, Vec<SyntaxRule>>,
}
impl std::fmt::Debug for SyntaxRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SyntaxRegistry")
            .field("token_count", &self.entries.len())
            .field("rule_count", &self.rule_count())
            .finish()
    }
}
impl Default for SyntaxRegistry {
    fn default() -> Self {
        Self::new()
    }
}
impl SyntaxRegistry {
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    pub fn register(&mut self, rule: SyntaxRule) {
        if rule.pattern.is_empty() {
            return;
        }
        for rules in self.entries.values_mut() {
            rules.retain(|existing| existing.name != rule.name);
        }
        let key = extract_leading_literal(&rule.pattern)
            .unwrap_or("")
            .to_owned();
        let bucket = self.entries.entry(key).or_default();
        let pos = bucket
            .iter()
            .position(|existing| existing.priority < rule.priority)
            .unwrap_or(bucket.len());
        bucket.insert(pos, rule);
    }

    #[must_use]
    pub fn lookup(&self, leading_token: &str) -> &[SyntaxRule] {
        self.entries.get(leading_token).map_or(&[], Vec::as_slice)
    }

    #[must_use]
    pub fn match_syntax(
        &self,
        category: SyntaxCategory,
        tokens: &[Token],
    ) -> Option<(usize, SyntaxMatch)> {
        (!tokens.is_empty()).then_some(())?;
        self.category_rules(category)
            .enumerate()
            .find_map(|(idx, rule)| match_pattern(&rule.pattern, tokens).map(|(_, m)| (idx, m)))
    }

    pub fn all_rules(&self) -> impl Iterator<Item = &SyntaxRule> + '_ {
        sorted_rules(self.entries.values().flat_map(|rules| rules.iter())).into_iter()
    }

    pub fn category_rules(&self, cat: SyntaxCategory) -> impl Iterator<Item = &SyntaxRule> + '_ {
        sorted_rules(
            self.entries
                .values()
                .flat_map(|rules| rules.iter())
                .filter(move |rule| rule.category == cat),
        )
        .into_iter()
    }

    #[must_use]
    pub fn rule_count(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }

    #[must_use]
    pub fn has_rules(&self, leading_token: &str) -> bool {
        self.entries
            .get(leading_token)
            .is_some_and(|rules| !rules.is_empty())
    }
}
/// Parse a syntax category name.
pub fn parse_syntax_category(s: &str) -> Result<SyntaxCategory, SyntaxError> {
    match s.to_ascii_lowercase().as_str() {
        "term" => Ok(SyntaxCategory::Term),
        "tactic" => Ok(SyntaxCategory::Tactic),
        "command" => Ok(SyntaxCategory::Command),
        "doelem" | "do_elem" => Ok(SyntaxCategory::Doelem),
        "level" => Ok(SyntaxCategory::Level),
        _ => Err(SyntaxError::UnknownCategory(s.to_owned())),
    }
}
/// Extract the first literal token from a syntax pattern.
#[must_use]
pub fn extract_leading_literal(pattern: &[SyntaxPatternItem]) -> Option<&str> {
    fn item_literal(item: &SyntaxPatternItem) -> Option<&str> {
        match item {
            SyntaxPatternItem::Literal(lit) => Some(lit.as_str()),
            SyntaxPatternItem::Optional(items) => extract_leading_literal(items),
            SyntaxPatternItem::Repetition { pattern, .. } => extract_leading_literal(pattern),
            SyntaxPatternItem::Variable { .. }
            | SyntaxPatternItem::CategoryRef(_)
            | SyntaxPatternItem::Precedence(_) => None,
        }
    }
    pattern.iter().find_map(item_literal)
}
fn sorted_rules<'a>(iter: impl Iterator<Item = &'a SyntaxRule>) -> Vec<&'a SyntaxRule> {
    let mut rules: Vec<_> = iter.collect();
    rules.sort_by(|a, b| {
        b.priority
            .cmp(&a.priority)
            .then_with(|| a.name.cmp(&b.name))
            .then_with(|| a.category.as_str().cmp(b.category.as_str()))
    });
    rules
}
fn match_pattern(pattern: &[SyntaxPatternItem], tokens: &[Token]) -> Option<(usize, SyntaxMatch)> {
    let (used, captures) = match_sequence(pattern, tokens)?;
    (used > 0).then(|| (used, collapse(captures)))
}
fn match_sequence(
    pattern: &[SyntaxPatternItem],
    tokens: &[Token],
) -> Option<(usize, Vec<SyntaxMatch>)> {
    let (mut used, mut captures) = (0, Vec::new());
    for item in pattern {
        let (step, capture) = match_item(item, &tokens[used..])?;
        used += step;
        if let Some(capture) = capture {
            captures.push(capture);
        }
    }
    Some((used, captures))
}

fn match_item(item: &SyntaxPatternItem, tokens: &[Token]) -> Option<(usize, Option<SyntaxMatch>)> {
    match item {
        SyntaxPatternItem::Literal(lit) => {
            let token = tokens.first()?;
            token_matches_literal(token, lit).then(|| (1, Some(SyntaxMatch::Token(lit.clone()))))
        }
        SyntaxPatternItem::Variable { category, .. } => {
            if let Some(cat) = category {
                parse_syntax_category(cat).ok()?;
            }
            token_expr(tokens.first()?).map(|expr| (1, Some(SyntaxMatch::Expr(expr))))
        }
        SyntaxPatternItem::CategoryRef(cat) => {
            parse_syntax_category(cat).ok()?;
            token_expr(tokens.first()?).map(|expr| (1, Some(SyntaxMatch::Expr(expr))))
        }
        SyntaxPatternItem::Optional(inner) => Some(match match_sequence(inner, tokens) {
            Some((used, captures)) => (
                used,
                Some(SyntaxMatch::Optional(Some(Box::new(collapse(captures))))),
            ),
            None => (0, Some(SyntaxMatch::Optional(None))),
        }),
        SyntaxPatternItem::Repetition {
            pattern,
            separator,
            at_least_one,
        } => match_repeat(pattern, separator.as_deref(), *at_least_one, tokens)
            .map(|(used, capture)| (used, Some(capture))),
        SyntaxPatternItem::Precedence(_) => Some((0, None)),
    }
}

fn match_repeat(
    pattern: &[SyntaxPatternItem],
    separator: Option<&str>,
    at_least_one: bool,
    tokens: &[Token],
) -> Option<(usize, SyntaxMatch)> {
    if pattern.is_empty() {
        return (!at_least_one).then(|| (0, SyntaxMatch::Repeat(Vec::new())));
    }
    let Some((first_used, first_caps)) = match_sequence(pattern, tokens) else {
        return (!at_least_one).then(|| (0, SyntaxMatch::Repeat(Vec::new())));
    };
    if first_used == 0 {
        return (!at_least_one).then(|| (0, SyntaxMatch::Repeat(Vec::new())));
    }
    let (mut used, mut items) = (first_used, vec![collapse(first_caps)]);
    loop {
        let next = match separator {
            Some(sep)
                if tokens
                    .get(used)
                    .is_some_and(|tok| token_matches_literal(tok, sep)) =>
            {
                used + 1
            }
            Some(_) => break,
            None => used,
        };
        let Some((step, caps)) = match_sequence(pattern, &tokens[next..]) else {
            break;
        };
        if step == 0 {
            break;
        }
        used = next + step;
        items.push(collapse(caps));
    }
    Some((used, SyntaxMatch::Repeat(items)))
}

fn collapse(mut captures: Vec<SyntaxMatch>) -> SyntaxMatch {
    if captures.len() == 1 {
        captures
            .pop()
            .expect("single-element capture vector should not be empty")
    } else {
        SyntaxMatch::Repeat(captures)
    }
}

fn token_matches_literal(token: &Token, literal: &str) -> bool {
    token_text(token).is_some_and(|text| {
        text == literal
            || matches!(
                (&token.kind, literal),
                (TokenKind::Arrow, "→")
                    | (TokenKind::Lambda, "λ")
                    | (TokenKind::Pi, "Π")
                    | (TokenKind::Turnstile, "⊢")
                    | (TokenKind::Ne, "≠")
                    | (TokenKind::Le, "≤")
                    | (TokenKind::Ge, "≥")
                    | (TokenKind::And, "∧")
                    | (TokenKind::Or, "∨")
                    | (TokenKind::Not, "¬")
            )
    })
}

fn token_expr(token: &Token) -> Option<SurfaceExpr> {
    match &token.kind {
        TokenKind::NatLit(n) => Some(SurfaceExpr::Lit(token.span, SurfaceLit::nat(n.clone()))),
        TokenKind::StringLit(s) => {
            Some(SurfaceExpr::Lit(token.span, SurfaceLit::String(s.clone())))
        }
        TokenKind::FloatLit(s) => Some(SurfaceExpr::Lit(token.span, SurfaceLit::Float(s.clone()))),
        TokenKind::CharLit(c) => Some(SurfaceExpr::Lit(token.span, SurfaceLit::Char(*c))),
        TokenKind::Underscore => Some(SurfaceExpr::Hole(token.span)),
        TokenKind::Eof | TokenKind::Error(_) => None,
        _ => token_text(token).map(|text| SurfaceExpr::Ident(token.span, text)),
    }
}

fn token_text(token: &Token) -> Option<String> {
    match &token.kind {
        TokenKind::Ident(s) | TokenKind::StringLit(s) | TokenKind::InterpolatedString(_, s) => {
            Some(s.clone())
        }
        TokenKind::SyntaxQuote(s) => Some(format!("`{s}")),
        TokenKind::NatLit(n) => Some(n.to_string()),
        kind => kind
            .as_keyword_str()
            .map(str::to_owned)
            .or_else(|| match kind {
                TokenKind::LParen => Some("(".to_owned()),
                TokenKind::RParen => Some(")".to_owned()),
                TokenKind::LBrace => Some("{".to_owned()),
                TokenKind::RBrace => Some("}".to_owned()),
                TokenKind::LBracket => Some("[".to_owned()),
                TokenKind::RBracket => Some("]".to_owned()),
                TokenKind::Colon => Some(":".to_owned()),
                TokenKind::ColonEq => Some(":=".to_owned()),
                TokenKind::Comma => Some(",".to_owned()),
                TokenKind::Dot => Some(".".to_owned()),
                TokenKind::Semicolon => Some(";".to_owned()),
                TokenKind::Arrow => Some("->".to_owned()),
                TokenKind::FatArrow => Some("=>".to_owned()),
                TokenKind::Lambda => Some("fun".to_owned()),
                TokenKind::Pi => Some("forall".to_owned()),
                TokenKind::At => Some("@".to_owned()),
                TokenKind::Hash => Some("#".to_owned()),
                TokenKind::Underscore => Some("_".to_owned()),
                TokenKind::Pipe => Some("|".to_owned()),
                TokenKind::Turnstile => Some("|-".to_owned()),
                TokenKind::Amp => Some("&".to_owned()),
                TokenKind::Star => Some("*".to_owned()),
                TokenKind::Plus => Some("+".to_owned()),
                TokenKind::Minus => Some("-".to_owned()),
                TokenKind::Slash => Some("/".to_owned()),
                TokenKind::Caret => Some("^".to_owned()),
                TokenKind::Eq => Some("=".to_owned()),
                TokenKind::Lt => Some("<".to_owned()),
                TokenKind::Gt => Some(">".to_owned()),
                TokenKind::Percent => Some("%".to_owned()),
                TokenKind::Eof | TokenKind::Error(_) => None,
                _ => None,
            }),
    }
}

#[cfg(test)]
#[path = "syntax_cmd_tests.rs"]
mod tests;
