// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The ONE reader of SMT-LIB2 formula text in trust-ir.
//!
//! Every place that reads an `smtlib2` formula as a term reads it here: the
//! contract grounder (`clean_expr_lowering::contract`, what a kernel replay
//! grounds), the clause free-name reader
//! ([`super::clause_typing::smt_free_symbols`]) and the `Linked` spec surface
//! ([`crate::spec_surface`]). A consumer that must know whether a text is one
//! it can trust a replay of calls [`read_smtlib_term`] rather than keeping
//! byte rules of its own, so what trust-ir grounds and what a consumer admits
//! are the same set by construction.
//!
//! # What it reads
//!
//! Exactly one SMT-LIB2 (2.6, §3.1) term built from these lexemes, and
//! nothing else:
//!
//! * whitespace: space, tab, line feed, carriage return — SMT-LIB2's four;
//! * `(` and `)`;
//! * a numeral (`0`, or a digit sequence with no leading `0`), a decimal
//!   (`numeral.digits`), a hexadecimal (`#x…`) or binary (`#b…`) literal;
//! * a simple symbol: letters, digits and `~ ! @ $ % ^ & * _ - + = < > . ? /`,
//!   not starting with a digit;
//! * a keyword (`:` then a simple symbol).
//!
//! Refused, each by name ([`SmtSourceDefect`]):
//!
//! * any other character: a non-ASCII character, and every control
//!   character but the four whitespace ones. Rust's `char::is_whitespace`
//!   also holds for vertical tab, form feed, NEL, NBSP, U+2028 and U+3000;
//!   no SMT-LIB2 reader treats them as whitespace, and splitting on them let
//!   `(>=\u{3000}5\u{3000}0)` be grounded as `(>= 5 0)`;
//! * a string literal (`"`), a quoted symbol (`|`) and a comment (`;`):
//!   SMT-LIB2 has them, and no trust-ir reader grounds any of them;
//! * an atom that is no SMT-LIB2 token: `x'` (a `'` is in no token — it is
//!   a successor-state marker in spec surface syntax, never a name), `007`
//!   (a numeral has no leading zero, and a symbol cannot start with a
//!   digit), `a,b`, `[`, `{`, a backslash, a backtick, `#z1`;
//! * unbalanced parentheses, an empty text, and more than one term;
//! * nesting deeper than [`MAX_SMTLIB_TERM_DEPTH`] (the reader is
//!   iterative, and every consumer that recurses over the term is bounded by
//!   it).
//!
//! # The normal form
//!
//! The term IS the normal form: two texts that read as the same
//! [`SmtSexp`] differ only in SMT-LIB2 whitespace, and
//! [`SmtSexp::canonical`] renders it with single spaces. A reader that
//! compares two formulas compares their terms, never their bytes and never a
//! rewriting of them.

/// The deepest parenthesis nesting [`read_smtlib_term`] accepts. Matches the
/// binary codec's `MAX_BINARY_NESTING_DEPTH`, so a term no reader can recurse
/// over without a stack overflow is refused rather than read.
pub const MAX_SMTLIB_TERM_DEPTH: usize = 256;

/// One SMT-LIB2 term as [`read_smtlib_term`] read it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtSexp<'a> {
    /// One token: a numeral, decimal, hexadecimal, binary, keyword or
    /// simple symbol, borrowed from the text.
    Atom(&'a str),
    /// A parenthesised list of terms.
    List(Vec<SmtSexp<'a>>),
}

impl SmtSexp<'_> {
    /// The canonical rendering: every list's items joined by one space.
    #[must_use]
    pub fn canonical(&self) -> String {
        self.canonical_with(|atom| atom)
    }

    /// [`Self::canonical`] with every atom replaced by `rename(atom)`
    /// (simultaneously, atoms only — a list is never renamed).
    #[must_use]
    pub fn canonical_with<'r>(&'r self, rename: impl Fn(&'r str) -> &'r str) -> String {
        fn render<'r>(
            term: &'r SmtSexp<'_>,
            rename: &dyn Fn(&'r str) -> &'r str,
            out: &mut String,
        ) {
            match term {
                SmtSexp::Atom(atom) => out.push_str(rename(atom)),
                SmtSexp::List(items) => {
                    out.push('(');
                    for (index, item) in items.iter().enumerate() {
                        if index > 0 {
                            out.push(' ');
                        }
                        render(item, rename, out);
                    }
                    out.push(')');
                }
            }
        }
        let mut out = String::new();
        render(self, &rename, &mut out);
        out
    }
}

/// Why a text is not one SMT-LIB2 term trust-ir reads
/// ([`read_smtlib_term`]). Every variant is a refusal: the text grounds
/// nothing, and a consumer admits nothing on it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtSourceDefect {
    /// A character outside SMT-LIB2 source: not printable ASCII and not one of
    /// its four whitespace characters.
    Character { offset: usize, character: char },
    /// A string literal, quoted symbol or comment — SMT-LIB2 lexemes no
    /// trust-ir reader grounds.
    Unread { offset: usize, lexeme: &'static str },
    /// An atom that is no SMT-LIB2 token.
    NotAToken { offset: usize, atom: String },
    /// Not exactly one balanced term.
    Shape(&'static str),
    /// Parentheses nested deeper than [`MAX_SMTLIB_TERM_DEPTH`].
    TooDeep,
}

impl core::fmt::Display for SmtSourceDefect {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Character { offset, character } => write!(
                f,
                "contains {character:?} (U+{:04X}) at byte {offset}, which is neither printable \
                 ASCII nor SMT-LIB2 whitespace (space, tab, line feed, carriage return)",
                u32::from(*character)
            ),
            Self::Unread { offset, lexeme } => write!(
                f,
                "contains a {lexeme} at byte {offset}, which no trust-ir reader grounds"
            ),
            Self::NotAToken { offset, atom } => write!(
                f,
                "contains `{atom}` at byte {offset}, which is no SMT-LIB2 token (not a numeral, \
                 decimal, `#x`/`#b` literal, keyword or simple symbol; a `'` is in none)"
            ),
            Self::Shape(what) => write!(f, "is not one SMT-LIB2 term: {what}"),
            Self::TooDeep => write!(
                f,
                "nests parentheses deeper than {MAX_SMTLIB_TERM_DEPTH} levels"
            ),
        }
    }
}

const fn is_smtlib_whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r')
}

/// SMT-LIB2's simple-symbol characters that are not letters or digits.
const fn is_symbol_punctuation(byte: u8) -> bool {
    matches!(
        byte,
        b'~' | b'!'
            | b'@'
            | b'$'
            | b'%'
            | b'^'
            | b'&'
            | b'*'
            | b'_'
            | b'-'
            | b'+'
            | b'='
            | b'<'
            | b'>'
            | b'.'
            | b'?'
            | b'/'
    )
}

fn is_simple_symbol(atom: &str) -> bool {
    let bytes = atom.as_bytes();
    !bytes.is_empty()
        && !bytes[0].is_ascii_digit()
        && bytes
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || is_symbol_punctuation(*b))
}

/// `0`, or digits with no leading `0` (SMT-LIB2's `⟨numeral⟩`).
fn is_numeral(atom: &str) -> bool {
    match atom.as_bytes() {
        [b'0'] => true,
        [first, rest @ ..] => (b'1'..=b'9').contains(first) && rest.iter().all(u8::is_ascii_digit),
        [] => false,
    }
}

/// Whether `atom` is one SMT-LIB2 token (a numeral, decimal, hexadecimal,
/// binary, keyword or simple symbol) — the atoms [`read_smtlib_term`] reads.
#[must_use]
pub fn is_smtlib_token(atom: &str) -> bool {
    let digits = |s: &str, ok: fn(u8) -> bool| !s.is_empty() && s.bytes().all(ok);
    if let Some(hex) = atom.strip_prefix("#x") {
        return digits(hex, |b| b.is_ascii_hexdigit());
    }
    if let Some(bin) = atom.strip_prefix("#b") {
        return digits(bin, |b| b == b'0' || b == b'1');
    }
    if let Some(keyword) = atom.strip_prefix(':') {
        return is_simple_symbol(keyword);
    }
    if let Some((whole, fraction)) = atom.split_once('.')
        && atom.bytes().next().is_some_and(|b| b.is_ascii_digit())
    {
        return is_numeral(whole) && digits(fraction, |b| b.is_ascii_digit());
    }
    is_numeral(atom) || is_simple_symbol(atom)
}

/// Read `text` as exactly one SMT-LIB2 term in the fragment the module docs
/// state, or say why it is not one.
///
/// # Errors
///
/// The first [`SmtSourceDefect`] in text order; the nesting depth and the
/// shape are checked as the term is built.
pub fn read_smtlib_term(text: &str) -> Result<SmtSexp<'_>, SmtSourceDefect> {
    let bytes = text.as_bytes();
    let mut stack: Vec<Vec<SmtSexp<'_>>> = vec![Vec::new()];
    let mut offset = 0usize;
    while offset < bytes.len() {
        let byte = bytes[offset];
        match byte {
            _ if is_smtlib_whitespace(byte) => offset += 1,
            b'(' => {
                if stack.len() > MAX_SMTLIB_TERM_DEPTH {
                    return Err(SmtSourceDefect::TooDeep);
                }
                stack.push(Vec::new());
                offset += 1;
            }
            b')' => {
                let items = stack
                    .pop()
                    .filter(|_| !stack.is_empty())
                    .ok_or(SmtSourceDefect::Shape("unbalanced `)`"))?;
                stack
                    .last_mut()
                    .ok_or(SmtSourceDefect::Shape("unbalanced `)`"))?
                    .push(SmtSexp::List(items));
                offset += 1;
            }
            b'"' => {
                return Err(SmtSourceDefect::Unread {
                    offset,
                    lexeme: "string literal",
                });
            }
            b'|' => {
                return Err(SmtSourceDefect::Unread {
                    offset,
                    lexeme: "quoted symbol",
                });
            }
            b';' => {
                return Err(SmtSourceDefect::Unread {
                    offset,
                    lexeme: "comment",
                });
            }
            b'!'..=b'~' => {
                let start = offset;
                while offset < bytes.len()
                    && matches!(bytes[offset], b'!'..=b'~')
                    && !matches!(bytes[offset], b'(' | b')' | b'"' | b'|' | b';')
                {
                    offset += 1;
                }
                let atom = &text[start..offset];
                if !is_smtlib_token(atom) {
                    return Err(SmtSourceDefect::NotAToken {
                        offset: start,
                        atom: atom.to_string(),
                    });
                }
                stack
                    .last_mut()
                    .ok_or(SmtSourceDefect::Shape("unbalanced `)`"))?
                    .push(SmtSexp::Atom(atom));
            }
            _ => {
                let character = text[offset..]
                    .chars()
                    .next()
                    .unwrap_or(char::REPLACEMENT_CHARACTER);
                return Err(SmtSourceDefect::Character { offset, character });
            }
        }
    }
    match (stack.pop(), stack.is_empty()) {
        (Some(mut roots), true) if roots.len() == 1 => Ok(roots.remove(0)),
        (Some(roots), true) if roots.is_empty() => Err(SmtSourceDefect::Shape("no term")),
        (Some(_), true) => Err(SmtSourceDefect::Shape("more than one term")),
        _ => Err(SmtSourceDefect::Shape("unbalanced `(`")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(text: &str) -> SmtSexp<'_> {
        SmtSexp::Atom(text)
    }

    #[test]
    fn reads_one_term_whitespace_aside() {
        let term = read_smtlib_term("(>=\t7\r\n 3)").unwrap();
        assert_eq!(term, SmtSexp::List(vec![atom(">="), atom("7"), atom("3")]));
        assert_eq!(term.canonical(), "(>= 7 3)");
        assert_eq!(read_smtlib_term("  x ").unwrap(), atom("x"));
        for token in [
            "0",
            "10",
            "1.05",
            "0.0",
            "#x0f",
            "#b01",
            ":named",
            "x.y",
            "a_b",
            "+",
            "<=",
            "bvadd",
            "~!@$%^&*_-+=<>.?/",
        ] {
            assert_eq!(read_smtlib_term(token), Ok(atom(token)), "{token}");
        }
    }

    /// Every character `char::is_whitespace` accepts beyond SMT-LIB2's four,
    /// and every other non-source character, is refused where it stands.
    #[test]
    fn a_character_outside_smtlib_source_is_refused() {
        for bad in [
            '\u{3000}', '\u{a0}', '\u{2003}', '\u{0b}', '\u{0c}', '\u{85}', '\u{2028}', '\u{2029}',
            '\u{1680}', '\u{0}', '\u{7f}', '\u{e4}',
        ] {
            let text = format!("(>={bad}5 0)");
            assert_eq!(
                read_smtlib_term(&text),
                Err(SmtSourceDefect::Character {
                    offset: 3,
                    character: bad
                }),
                "{text:?}"
            );
        }
    }

    #[test]
    fn strings_quoted_symbols_and_comments_are_unread() {
        assert!(matches!(
            read_smtlib_term("(= s \"a\")"),
            Err(SmtSourceDefect::Unread {
                lexeme: "string literal",
                ..
            })
        ));
        assert!(matches!(
            read_smtlib_term("(>= |x'| 0)"),
            Err(SmtSourceDefect::Unread {
                lexeme: "quoted symbol",
                ..
            })
        ));
        assert!(matches!(
            read_smtlib_term("(>= x 0) ; true"),
            Err(SmtSourceDefect::Unread {
                lexeme: "comment",
                ..
            })
        ));
    }

    /// `x'` is no SMT-LIB2 token: z3 reports "unexpected character" and drops
    /// the assertion, while a reader that allowed `'` in a name grounded it.
    #[test]
    fn an_atom_that_is_no_token_is_refused() {
        for (text, bad) in [
            ("(>= x' 0)", "x'"),
            ("(<= 0 r'')", "r''"),
            ("(>= a'b 0)", "a'b"),
            ("(>= 007 3)", "007"),
            ("(= 05 5)", "05"),
            ("(f a,b)", "a,b"),
            ("(f [x])", "[x]"),
            ("(f {x})", "{x}"),
            ("(f a\\b)", "a\\b"),
            ("(f `x`)", "`x`"),
            ("(f #z1)", "#z1"),
            ("(f #x)", "#x"),
            ("(f 1.)", "1."),
            ("(f 01.5)", "01.5"),
            ("(f :)", ":"),
            ("(f 1x)", "1x"),
        ] {
            assert!(
                matches!(read_smtlib_term(text), Err(SmtSourceDefect::NotAToken { ref atom, .. }) if atom == bad),
                "{text}: {:?}",
                read_smtlib_term(text)
            );
        }
    }

    #[test]
    fn exactly_one_balanced_term() {
        for (text, what) in [
            ("", "no term"),
            ("   ", "no term"),
            ("x y", "more than one term"),
            ("(>= x 0) (>= y 0)", "more than one term"),
            ("(>= x 0", "unbalanced `(`"),
            ("(>= x 0))", "unbalanced `)`"),
            (")", "unbalanced `)`"),
        ] {
            assert_eq!(
                read_smtlib_term(text),
                Err(SmtSourceDefect::Shape(what)),
                "{text}"
            );
        }
        assert_eq!(read_smtlib_term("()"), Ok(SmtSexp::List(Vec::new())));
    }

    #[test]
    fn nesting_is_bounded_without_recursion() {
        let nested = |n: usize| format!("{}x{}", "(not ".repeat(n), ")".repeat(n));
        assert!(read_smtlib_term(&nested(MAX_SMTLIB_TERM_DEPTH)).is_ok());
        assert_eq!(
            read_smtlib_term(&nested(MAX_SMTLIB_TERM_DEPTH + 1)),
            Err(SmtSourceDefect::TooDeep)
        );
        assert_eq!(
            read_smtlib_term(&"(".repeat(1_000_000)),
            Err(SmtSourceDefect::TooDeep)
        );
    }

    #[test]
    fn canonical_with_renames_atoms_only() {
        let term = read_smtlib_term("(and (<= a  7)\n(= b a))").unwrap();
        assert_eq!(
            term.canonical_with(|atom| if atom == "a" { "seq" } else { atom }),
            "(and (<= seq 7) (= b seq))"
        );
    }
}
