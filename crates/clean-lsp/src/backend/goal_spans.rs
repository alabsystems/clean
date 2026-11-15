// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cursor coverage for actual observed states. No context or goal is inferred
//! from tokens: they supply only delimiters omitted by attribution/term spans.

use clean_elab::tactic::{TacticGoalObservation, TacticGoalObservationKind};
use clean_parser::lexer::{Lexer, Token, TokenKind};

struct Delimiters {
    tokens: Vec<Token>,
    mates: Vec<Option<usize>>,
}

fn delimiter(kind: &TokenKind) -> Option<(u8, bool)> {
    match kind {
        TokenKind::LParen => Some((0, true)),
        TokenKind::RParen => Some((0, false)),
        TokenKind::LBracket => Some((1, true)),
        TokenKind::RBracket | TokenKind::RBracketPrime => Some((1, false)),
        TokenKind::LBrace => Some((2, true)),
        TokenKind::RBrace => Some((2, false)),
        TokenKind::LAngle => Some((3, true)),
        TokenKind::RAngle => Some((3, false)),
        TokenKind::StrictLBrace => Some((4, true)),
        TokenKind::StrictRBrace => Some((4, false)),
        _ => None,
    }
}

impl Delimiters {
    fn new(text: &str) -> Self {
        let tokens = Lexer::tokenize(text);
        let mut mates = vec![None; tokens.len()];
        let mut stack = Vec::new();
        for (index, token) in tokens.iter().enumerate() {
            if matches!(token.kind, TokenKind::Error(_)) {
                stack.clear();
            }
            if let Some((kind, open)) = delimiter(&token.kind) {
                if open {
                    stack.push((kind, index));
                } else if let Some((opening_kind, opening)) = stack.pop() {
                    if opening_kind == kind {
                        mates[opening] = Some(index);
                        mates[index] = Some(opening);
                    } else {
                        stack.clear();
                    }
                }
            }
        }
        Self { tokens, mates }
    }

    fn end(&self, start: usize, mut end: usize, rewrite_rules: bool) -> usize {
        let mut index = self.tokens.partition_point(|token| token.span.end <= end);
        // Only actual Rw/Rewrite/Rwa observations set after_at_tail. Their parser
        // retains a head span, so include their immediately following rule list
        // (including []) before applying the ordinary owned-closer rule.
        if rewrite_rules {
            if let Some(token) = self.tokens.get(index) {
                if token.span.start >= end && matches!(token.kind, TokenKind::LBracket) {
                    if let Some(close) = self.mates[index] {
                        end = self.tokens[close].span.end;
                        index = close + 1;
                    }
                }
            }
        }
        while let Some(token) = self.tokens.get(index) {
            if token.span.start < end || !matches!(delimiter(&token.kind), Some((_, false))) {
                break;
            }
            let Some(opening) = self.mates[index] else {
                break;
            };
            let opening_start = self.tokens[opening].span.start;
            if opening_start < start || opening_start >= end {
                break;
            }
            end = token.span.end;
            index += 1;
        }
        end
    }
}

pub(super) fn complete_observation_spans(text: &str, observations: &mut [TacticGoalObservation]) {
    if observations.is_empty() {
        return;
    }
    let delimiters = Delimiters::new(text);
    for observation in observations {
        let span = &mut observation.tactic_range;
        if observation.kind == TacticGoalObservationKind::Tactic
            && span.start < span.end
            && text.get(span.start..span.end).is_some()
        {
            span.end = delimiters.end(span.start, span.end, observation.after_at_tail);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Delimiters;

    #[test]
    fn rewrite_rule_lists_use_real_matching_tokens_including_empty_lists() {
        for text in [
            "rw []",
            "rw [h]",
            "rwa []",
            "rwa [h]",
            "rewrite [(f \"]\"), h]",
        ] {
            let head_end = text.find(' ').unwrap();
            assert_eq!(Delimiters::new(text).end(0, head_end, true), text.len());
        }
    }

    #[test]
    fn owned_closers_do_not_consume_enclosing_term_delimiters() {
        let text = "(by exact (by exact hp))";
        let end = text.find("hp").unwrap() + 2;
        let delimiters = Delimiters::new(text);
        assert_eq!(
            delimiters.end(text.find("exact").unwrap(), end, false),
            text.len() - 1
        );
        assert_eq!(
            delimiters.end(text.rfind("exact").unwrap(), end, false),
            end
        );
    }

    #[test]
    fn comments_strings_and_mismatched_closers_do_not_invent_ownership() {
        let text = "exact (f \")\" /- ) -/ hp) next";
        let end = text.find("hp").unwrap() + 2;
        assert_eq!(
            Delimiters::new(text).end(0, end, false),
            text.find(") next").unwrap() + 1
        );
        for text in ["exact hp) next", "exact (hp] ) next"] {
            let end = text.find("hp").unwrap() + 2;
            assert_eq!(Delimiters::new(text).end(0, end, false), end);
        }
    }
}
