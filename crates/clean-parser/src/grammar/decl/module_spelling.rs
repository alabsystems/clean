// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pinned Lean's verdict on a modifier prefix in front of `import`, `section`
//! or `variable`, or in front of a `module` that is not the file's first token
//! (plan item `formats-module-spelling-refusals`).
//!
//! Clean's declaration parser accumulates modifiers (`private`, `public`,
//! `noncomputable`, `@[…]`, …) before it looks at the command keyword, and
//! these three commands used to drop them: `private import X`, `private
//! section` and `public variable` parsed as their bare forms. In pinned Lean
//! v4.30.0-rc2 a prefix is read by whichever command parsers can start with it
//! (`Lean/Parser/Command.lean`, `Syntax.lean`), each taking its modifiers in a
//! fixed order:
//!
//! - every declaration, `initialize` and `builtin_initialize`: `declModifiers`
//!   (doc comment? `@[…]`? visibility? `protected`? (`meta` |
//!   `noncomputable`)? `unsafe`? (`partial` | `nonrec`)?), and `instance`
//!   takes an `attrKind` after it;
//! - `section`: `sectionHeader` (`@[expose]`? `public`? `noncomputable`?
//!   `meta`?), with no doc comment;
//! - `syntax` abbreviations: doc comment? visibility?;
//! - `syntax`, `macro`, `notation` and the other attribute-taking commands:
//!   doc comment? `@[…]`? `attrKind`?; the `simproc` family and `unif_hint`:
//!   doc comment? `attrKind`; `grind_pattern`: `attrKind` alone;
//! - `#guard_msgs`, `declare_syntax_cat`, the `*_decl` simprocs and the other
//!   doc-only commands: doc comment? (`add_decl_doc`'s is mandatory);
//! - from v4.36.0-rc1 (lean4#15518), `variable`: a visibility alone.
//!
//! A declaration doc comment (`/-- … -/`) is a token in Lean and trivia in
//! Clean's lexer, so the model reads the first declaration doc comment in the
//! gap before the command's first token (no token between) as the prefix's
//! first word, when the command before it does not take it as its last
//! argument (`decl::doc_before`). A doc
//! comment of either kind after the first word (`public /-- d -/ import`,
//! `private /-! d -/ section`, `/-- a -/ /-! b -/ section`) is a token no
//! reader takes, so Lean stops there with "unexpected token '/--'" (or
//! `'/-!'`), naming the first of two in a row (`decl::doc_before`'s
//! `doc_met_before`; before the first token, `doc_before`'s
//! `DocBefore::Stacked`). Such a prefix also ends the file header
//! (`decl::header`), which is how `module` / `public /-- d -/ import Init`
//! reaches this model.
//!
//! Lean stops at the first token no surviving parser takes and reports
//! "unexpected token '<t>'; expected <keywords>", where the keywords are the
//! next MANDATORY token of each parser still alive (an optional modifier slot
//! that fails without consuming input contributes nothing), sorted, at the end
//! of the token before `<t>` (the end of the doc comment, when that is the
//! word before). The parser reproduces the first message of 160 of the 168
//! rows of `tests/fixtures/module_spellings/modifier_matrix.tsv` (v4.30.0-rc2
//! and v4.33.1 alike) through this model. The other eight put
//! `meta` in front of `section` or `variable`, which the dispatcher's `meta`
//! arm does not take, so they never reach it (pinned in
//! `crates/clean-parser/tests/module_system_b_e2e_support/verdict_tables.rs`).
//! The lists are those of a file that
//! imports only `Init`; Mathlib adds declaration commands, so Lean's list is
//! longer there while the verdict and position agree.

use super::super::Parser;
use super::doc_before::DocBefore;
use crate::lexer::TokenKind;
use crate::ParseError;

/// The commands whose modifier prefix is checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::grammar) enum GuardedCommand {
    /// `import` after the header has ended.
    Import,
    /// `section`.
    Section,
    /// `variable`.
    Variable,
    /// An identifier where a command keyword belongs: a `module` behind a doc
    /// comment, which the header does not read.
    Identifier,
    /// The input ended after a declaration doc comment opened a command.
    Eof,
}

impl GuardedCommand {
    /// Lean's words for this token where it is unexpected.
    fn unexpected(self) -> &'static str {
        match self {
            Self::Import => "unexpected token 'import'",
            Self::Section => "unexpected token 'section'",
            Self::Variable => "unexpected token 'variable'",
            Self::Identifier => "unexpected identifier",
            Self::Eof => "unexpected end of input",
        }
    }
}

/// One word of a modifier prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Word {
    /// A declaration doc comment (`/-- … -/`), only ever the first word.
    DocComment,
    /// A doc comment of either kind after the first word, which no reader
    /// takes: `token` is the atom Lean names there (`/--` or `/-!`).
    LateDoc {
        token: &'static str,
    },
    /// One `@[…]` block; `expose_only` when it is exactly `@[expose]`.
    Attributes {
        expose_only: bool,
    },
    Private,
    Public,
    Protected,
    Meta,
    Noncomputable,
    Unsafe,
    Partial,
    /// `scoped` or `local`.
    AttrKind,
}

/// The command parsers a prefix can still be read by.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reader {
    Declaration,
    SectionHeader,
    SyntaxAbbrev,
    AttrCommands,
    /// doc comment? `attrKind`, then the keyword.
    DocAttrKindCommands,
    /// `attrKind`, then the keyword.
    GrindPattern,
    /// doc comment?, then the keyword.
    DocOnlyCommands,
    /// The qualified rc2 parser takes only optional visibility before
    /// `variable` (Command.lean); it has no declaration-doc slot.
    VisibleVariable,
}

const DECLARATION: &[&str] = &[
    "abbrev",
    "axiom",
    "builtin_initialize",
    "class",
    "coinductive",
    "def",
    "example",
    "inductive",
    "initialize",
    "instance",
    "opaque",
    "structure",
    "theorem",
];
const ATTR_COMMANDS: &[&str] = &[
    "binder_predicate",
    "elab",
    "elab_rules",
    "infix",
    "infixl",
    "infixr",
    "macro",
    "macro_rules",
    "notation",
    "postfix",
    "prefix",
    "syntax",
];
const DOC_ATTR_KIND_COMMANDS: &[&str] = &[
    "builtin_cbv_simproc",
    "builtin_dsimproc",
    "builtin_simproc",
    "cbv_simproc",
    "dsimproc",
    "simproc",
    "unif_hint",
];
const DOC_ONLY_COMMANDS: &[&str] = &[
    "#guard_msgs",
    "add_decl_doc",
    "builtin_cbv_simproc_decl",
    "builtin_dsimproc_decl",
    "builtin_grind_propagator",
    "builtin_simproc_decl",
    "cbv_simproc_decl",
    "declare_simp_like_tactic",
    "declare_syntax_cat",
    "dsimproc_decl",
    "grind_propagator",
    "recommended_spelling",
    "register_error_explanation",
    "register_tactic_tag",
    "register_try?_tactic",
    "simproc_decl",
    "tactic_extension",
];

/// `instance`'s `attrKind` slot, after the whole of `declModifiers`.
const INSTANCE_ATTR_KIND_SLOT: u8 = 7;

impl Reader {
    /// The slot `word` fills in this reader's modifier order, if it takes it.
    fn slot(self, word: Word) -> Option<u8> {
        match (self, word) {
            (
                Self::Declaration
                | Self::SyntaxAbbrev
                | Self::AttrCommands
                | Self::DocAttrKindCommands
                | Self::DocOnlyCommands,
                Word::DocComment,
            ) => Some(0),
            (Self::Declaration, Word::Attributes { .. }) => Some(1),
            (Self::Declaration, Word::Private | Word::Public) => Some(2),
            (Self::Declaration, Word::Protected) => Some(3),
            (Self::Declaration, Word::Meta | Word::Noncomputable) => Some(4),
            (Self::Declaration, Word::Unsafe) => Some(5),
            (Self::Declaration, Word::Partial) => Some(6),
            (Self::Declaration, Word::AttrKind) => Some(INSTANCE_ATTR_KIND_SLOT),
            (Self::SectionHeader, Word::Attributes { expose_only: true }) => Some(0),
            (Self::SectionHeader, Word::Public) => Some(1),
            (Self::SectionHeader, Word::Noncomputable) => Some(2),
            (Self::SectionHeader, Word::Meta) => Some(3),
            (Self::SyntaxAbbrev, Word::Private | Word::Public) => Some(1),
            (Self::VisibleVariable, Word::Private | Word::Public) => Some(0),
            (Self::AttrCommands, Word::Attributes { .. }) => Some(1),
            (Self::AttrCommands, Word::AttrKind) => Some(2),
            (Self::DocAttrKindCommands, Word::AttrKind) => Some(1),
            (Self::GrindPattern, Word::AttrKind) => Some(0),
            _ => None,
        }
    }

    /// The keywords this reader expects next, having filled `last`.
    fn expected(self, last: Option<u8>) -> &'static [&'static str] {
        match self {
            Self::Declaration if last == Some(INSTANCE_ATTR_KIND_SLOT) => &["instance"],
            Self::Declaration => DECLARATION,
            Self::SectionHeader => &["section"],
            Self::SyntaxAbbrev => &["syntax"],
            Self::AttrCommands => ATTR_COMMANDS,
            Self::DocAttrKindCommands => DOC_ATTR_KIND_COMMANDS,
            Self::GrindPattern => &["grind_pattern"],
            Self::DocOnlyCommands => DOC_ONLY_COMMANDS,
            Self::VisibleVariable => &["variable"],
        }
    }

    fn takes(self, command: GuardedCommand) -> bool {
        matches!(
            (self, command),
            (Self::SectionHeader, GuardedCommand::Section)
                | (Self::VisibleVariable, GuardedCommand::Variable)
        )
    }
}

/// Where Lean stops reading a prefix, and what it expected there.
#[derive(Debug, PartialEq, Eq)]
struct Refusal {
    /// The index of the word Lean stops at, or `words.len()` for the command
    /// keyword.
    at: usize,
    expected: Vec<&'static str>,
}

type ReaderStates = Vec<(Reader, Option<u8>)>;

fn expected_keywords(alive: &[(Reader, Option<u8>)]) -> Vec<&'static str> {
    let mut keywords: Vec<&'static str> = alive
        .iter()
        .flat_map(|(reader, last)| reader.expected(*last).iter().copied())
        .collect();
    keywords.sort_unstable();
    keywords.dedup();
    keywords
}

/// Read only the prefix. A refused prefix does not reach the command parser.
fn read_prefix(words: &[Word], variable_visibility: bool) -> Result<ReaderStates, Refusal> {
    let mut alive: Vec<(Reader, Option<u8>)> = [
        Reader::Declaration,
        Reader::SectionHeader,
        Reader::SyntaxAbbrev,
        Reader::AttrCommands,
        Reader::DocAttrKindCommands,
        Reader::GrindPattern,
        Reader::DocOnlyCommands,
    ]
    .into_iter()
    .chain(variable_visibility.then_some(Reader::VisibleVariable))
    .map(|reader| (reader, None))
    .collect();
    for (at, word) in words.iter().enumerate() {
        let next: Vec<(Reader, Option<u8>)> = alive
            .iter()
            .filter_map(|(reader, last)| {
                let slot = reader.slot(*word)?;
                last.is_none_or(|last| slot > last)
                    .then_some((*reader, Some(slot)))
            })
            .collect();
        if next.is_empty() {
            return Err(Refusal {
                at,
                expected: expected_keywords(&alive),
            });
        }
        alive = next;
    }
    Ok(alive)
}

/// Lean's verdict on `words` followed by `command`: `None` when it accepts.
fn lean_verdict(
    words: &[Word],
    command: GuardedCommand,
    variable_visibility: bool,
) -> Option<Refusal> {
    let alive = match read_prefix(words, variable_visibility) {
        Ok(alive) => alive,
        Err(refusal) => return Some(refusal),
    };
    if alive.iter().any(|(reader, _)| reader.takes(command)) {
        return None;
    }
    Some(Refusal {
        at: words.len(),
        expected: expected_keywords(&alive),
    })
}

/// Lean's rendering of an expected list: `'a'`, `'a' or 'b'`, `'a', 'b' or 'c'`.
fn render_expected(keywords: &[&str]) -> String {
    let quoted: Vec<String> = keywords.iter().map(|k| format!("'{k}'")).collect();
    match quoted.split_last() {
        None => String::new(),
        Some((last, [])) => last.clone(),
        Some((last, init)) => format!("{} or {last}", init.join(", ")),
    }
}

impl Parser {
    /// A second doc after a declaration doc is refused before reading any
    /// command or attribute. Reuse the prefix model without inventing a
    /// command keyword: the second doc already leaves no surviving reader.
    pub(in crate::grammar) fn leading_stacked_doc_refusal(&self) -> Option<ParseError> {
        let DocBefore::Stacked { end, next } = self.doc_before(self.command_start)? else {
            return None;
        };
        let variable_visibility = self.variable_visibility();
        let refusal = read_prefix(
            &[Word::DocComment, Word::LateDoc { token: next }],
            variable_visibility,
        )
        .err()?;
        let (line, col) = self.line_col_at(end);
        Some(ParseError::ModuleSyntaxRefused {
            line,
            col,
            message: format!(
                "unexpected token '{next}'; expected {}",
                render_expected(&refusal.expected)
            ),
        })
    }

    /// A declaration doc comment opens a command even when the lexer has
    /// skipped it immediately before EOF. Module docs and note arguments
    /// remain complete commands, as classified by the existing doc reader.
    pub(in crate::grammar) fn eof_declaration_doc_refusal(&mut self) -> Option<ParseError> {
        if !matches!(self.current_kind(), TokenKind::Eof)
            || !matches!(
                self.doc_before(self.pos),
                Some(DocBefore::Declaration { .. } | DocBefore::Stacked { .. })
            )
        {
            return None;
        }
        let outer_command_start = std::mem::replace(&mut self.command_start, self.pos);
        let refusal = self.modifier_prefix_refusal(GuardedCommand::Eof);
        self.command_start = outer_command_start;
        refusal
    }

    /// Pinned Lean's refusal of the modifiers in front of `command` (the
    /// current token), or `None` when Lean takes them. Called only when the
    /// command has a prefix ([`Parser::has_modifier_prefix`]).
    pub(in crate::grammar) fn modifier_prefix_refusal(
        &self,
        command: GuardedCommand,
    ) -> Option<ParseError> {
        let variable_visibility = self.variable_visibility();
        let Some((words, doc_end)) = self.prefix_words() else {
            // A prefix token the model does not know: refuse, in Clean's words.
            let token = self.current();
            return Some(ParseError::ModuleSyntaxRefused {
                line: token.line as usize,
                col: token.col as usize,
                message: format!(
                    "{}; Clean has no model of the modifiers in front of it",
                    command.unexpected()
                ),
            });
        };
        let refusal = lean_verdict(
            &words.iter().map(|(word, _)| *word).collect::<Vec<_>>(),
            command,
            variable_visibility,
        )?;
        let (stop_token, unexpected) = match words.get(refusal.at) {
            Some((Word::Attributes { .. }, index)) => (*index, "unexpected token '@['".to_owned()),
            Some((Word::LateDoc { token }, index)) => {
                (*index, format!("unexpected token '{token}'"))
            }
            Some((_, index)) => (
                *index,
                format!("unexpected token '{}'", self.token_text(*index)),
            ),
            None => (self.pos, command.unexpected().to_owned()),
        };
        // Lean reports an unexpected token at the end of the token before it
        // (the start of that token's trailing whitespace, `mkErrorMessage`):
        // the doc comment, when that is the word before the stop, and
        // otherwise the token before the stop's. The first word is always a
        // doc comment or a declaration modifier, so a word before the stop
        // exists; the stop's own start stands in if it ever did not.
        let doc_was_last = refusal
            .at
            .checked_sub(1)
            .and_then(|previous| words.get(previous))
            .is_some_and(|(word, _)| *word == Word::DocComment);
        let (line, col) = match (command, refusal.at == words.len()) {
            // An unfinished doc prefix reaches the actual EOF position.
            // Stacked docs still stop at the end of the first doc instead.
            (GuardedCommand::Eof, true) => {
                (self.current().line as usize, self.current().col as usize)
            }
            _ => match doc_end.filter(|_| doc_was_last) {
                Some(end) => self.line_col_at(end),
                None => stop_token
                    .checked_sub(1)
                    .and_then(|before| self.token_end_position(before))
                    .unwrap_or_else(|| (self.current().line as usize, self.current().col as usize)),
            },
        };
        Some(ParseError::ModuleSyntaxRefused {
            line,
            col,
            message: format!(
                "{unexpected}; expected {}",
                render_expected(&refusal.expected)
            ),
        })
    }

    /// Lean's position of byte `offset`: its 1-based line and its 0-based
    /// column in codepoints (`FileMap.toPosition`).
    fn line_col_at(&self, offset: usize) -> (usize, usize) {
        let before = self.source.get(..offset).unwrap_or_default();
        let line_start = before.rfind('\n').map_or(0, |newline| newline + 1);
        let line = before.matches('\n').count() + 1;
        let col = before
            .get(line_start..)
            .map_or(0, |text| text.chars().count());
        (line, col)
    }

    /// The words of the prefix: the declaration doc comment the command
    /// carries ([`Parser::doc_before`]), if any, then the tokens
    /// `self.tokens[self.command_start..self.pos]`; each with its first
    /// token's index (the command's first token, for the doc comment), and the
    /// doc comment's end byte. A doc comment of either kind ending before a
    /// later token, the command's keyword included, is the last word
    /// ([`Word::LateDoc`], with the index of the token after it): Lean stops
    /// there (measured on pinned v4.30.0-rc2: `private /-- d -/ section` at
    /// the end of `private`, "unexpected token '/--'"), at the first of two in
    /// a row (`private /-! a -/ /-- b -/ section`: "unexpected token '/-!'").
    /// So is a doc comment after the carried one, before the first token
    /// (`/-- a -/ /-! b -/ private section`: `2:8`, the end of `/-- a -/`,
    /// "unexpected token '/-!'; expected '#guard_msgs', …").
    /// `None` when a token is not one the model knows.
    fn prefix_words(&self) -> Option<(Vec<(Word, usize)>, Option<usize>)> {
        let mut words = Vec::new();
        let doc_end = match self.doc_before(self.command_start) {
            Some(DocBefore::Declaration { end }) => {
                words.push((Word::DocComment, self.command_start));
                Some(end)
            }
            // Another doc comment after the first is the second word, and
            // Lean stops there, before any modifier token.
            Some(DocBefore::Stacked { end, next }) => {
                words.push((Word::DocComment, self.command_start));
                words.push((Word::LateDoc { token: next }, self.command_start));
                return Some((words, Some(end)));
            }
            Some(DocBefore::Module) | None => None,
        };
        let mut index = self.command_start;
        loop {
            let late_doc = self
                .doc_met_before(index)
                .filter(|_| index > self.command_start);
            if let Some(doc) = late_doc {
                let token = doc.lean_token();
                words.push((Word::LateDoc { token }, index));
                break;
            }
            if index >= self.pos {
                break;
            }
            let token = self.tokens.get(index)?;
            let word = match &token.kind {
                TokenKind::At => {
                    let (end, expose_only) = self.attribute_block(index)?;
                    words.push((Word::Attributes { expose_only }, index));
                    index = end + 1;
                    continue;
                }
                TokenKind::Private => Word::Private,
                TokenKind::Public => Word::Public,
                TokenKind::Protected => Word::Protected,
                TokenKind::Noncomputable => Word::Noncomputable,
                TokenKind::Unsafe => Word::Unsafe,
                TokenKind::Partial => Word::Partial,
                TokenKind::Scoped => Word::AttrKind,
                TokenKind::Ident(name) if !token.ident_escaped && name == "local" => Word::AttrKind,
                TokenKind::Ident(name) if !token.ident_escaped && name == "meta" => Word::Meta,
                _ => return None,
            };
            words.push((word, index));
            index += 1;
        }
        Some((words, doc_end))
    }

    /// The `@[…]` block opening at token `at`: its closing `]`'s index, and
    /// whether it is exactly `@[expose]`.
    fn attribute_block(&self, at: usize) -> Option<(usize, bool)> {
        if !matches!(self.tokens.get(at + 1)?.kind, TokenKind::LBracket) {
            return None;
        }
        let mut depth = 0usize;
        for index in at + 1..self.pos {
            match self.tokens.get(index)?.kind {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        let expose_only = index == at + 3
                            && self.tokens.get(at + 2).is_some_and(|token| {
                                matches!(&token.kind, TokenKind::Ident(name) if name == "expose")
                                    && !token.ident_escaped
                            });
                        return Some((index, expose_only));
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// The source text of token `index`.
    fn token_text(&self, index: usize) -> &str {
        self.tokens
            .get(index)
            .and_then(|token| self.source.get(token.span.start..token.span.end))
            .unwrap_or("")
    }
}

#[cfg(test)]
#[path = "module_spelling_tests.rs"]
mod tests;
