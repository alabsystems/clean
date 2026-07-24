// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! UTF-8-safe s-expression parsing and re-serialization.
//!
//! SerAPI answers can carry unicode identifiers; this parser slices at ASCII
//! delimiters only, so multibyte sequences round-trip byte-faithfully. The
//! serializer quotes atoms containing delimiters so dumped payloads re-parse
//! identically through the importer's tokenizer (which shares the same
//! escape rules: `\n`, `\t`, `\\`, `\"`).

use clean_mathverse::coq::alpha::Sexp;

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// Parse a single s-expression, preserving multibyte UTF-8 atoms.
pub fn parse_sexp_utf8(input: &str) -> Result<Sexp, String> {
    let mut p = Parser {
        b: input.as_bytes(),
        s: input,
        i: 0,
    };
    p.skip_ws();
    let out = p.parse_one()?;
    p.skip_ws();
    if p.i < p.b.len() {
        return Err(format!("trailing input at byte {}", p.i));
    }
    Ok(out)
}

struct Parser<'a> {
    b: &'a [u8],
    s: &'a str,
    i: usize,
}

impl Parser<'_> {
    fn skip_ws(&mut self) {
        while self.i < self.b.len() {
            match self.b[self.i] {
                b' ' | b'\t' | b'\n' | b'\r' => self.i += 1,
                b';' => {
                    while self.i < self.b.len() && self.b[self.i] != b'\n' {
                        self.i += 1;
                    }
                }
                _ => break,
            }
        }
    }

    fn parse_one(&mut self) -> Result<Sexp, String> {
        self.skip_ws();
        if self.i >= self.b.len() {
            return Err("unexpected end of input".to_string());
        }
        match self.b[self.i] {
            b'(' => {
                self.i += 1;
                let mut items = Vec::new();
                loop {
                    self.skip_ws();
                    if self.i >= self.b.len() {
                        return Err("unclosed list".to_string());
                    }
                    if self.b[self.i] == b')' {
                        self.i += 1;
                        return Ok(Sexp::List(items));
                    }
                    items.push(self.parse_one()?);
                }
            }
            b')' => Err(format!("unexpected ')' at byte {}", self.i)),
            b'"' => self.parse_quoted(),
            _ => self.parse_bare(),
        }
    }

    fn parse_quoted(&mut self) -> Result<Sexp, String> {
        // self.b[self.i] == b'"'
        self.i += 1;
        let mut bytes: Vec<u8> = Vec::new();
        while self.i < self.b.len() && self.b[self.i] != b'"' {
            if self.b[self.i] == b'\\' && self.i + 1 < self.b.len() {
                self.i += 1;
                match self.b[self.i] {
                    b'n' => bytes.push(b'\n'),
                    b't' => bytes.push(b'\t'),
                    b'\\' => bytes.push(b'\\'),
                    b'"' => bytes.push(b'"'),
                    other => {
                        bytes.push(b'\\');
                        bytes.push(other);
                    }
                }
            } else {
                bytes.push(self.b[self.i]);
            }
            self.i += 1;
        }
        if self.i >= self.b.len() {
            return Err("unclosed string".to_string());
        }
        self.i += 1;
        Ok(Sexp::Atom(String::from_utf8_lossy(&bytes).into_owned()))
    }

    fn parse_bare(&mut self) -> Result<Sexp, String> {
        let start = self.i;
        while self.i < self.b.len()
            && !matches!(
                self.b[self.i],
                b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b'"'
            )
        {
            self.i += 1;
        }
        // Delimiters are all ASCII, so slicing here is UTF-8 safe.
        Ok(Sexp::Atom(self.s[start..self.i].to_string()))
    }
}

// ---------------------------------------------------------------------------
// Serialization
// ---------------------------------------------------------------------------

/// Serialize an s-expression, quoting atoms that contain delimiters.
pub fn sexp_to_string(s: &Sexp) -> String {
    let mut out = String::new();
    write_sexp(s, &mut out);
    out
}

fn write_sexp(s: &Sexp, out: &mut String) {
    match s {
        Sexp::Atom(a) => write_atom(a, out),
        Sexp::List(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                write_sexp(item, out);
            }
            out.push(')');
        }
    }
}

fn needs_quote(a: &str) -> bool {
    a.is_empty()
        || a.chars()
            .any(|c| matches!(c, ' ' | '\t' | '\n' | '\r' | '(' | ')' | '"' | '\\' | ';'))
}

fn write_atom(a: &str, out: &mut String) {
    if !needs_quote(a) {
        out.push_str(a);
        return;
    }
    out.push('"');
    for c in a.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            other => out.push(other),
        }
    }
    out.push('"');
}

/// Quote a string for embedding in a sertop command (always quoted).
pub fn quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_sexp_utf8_unicode_atom_roundtrips() {
        let src = "(Id αβ_γ)";
        let parsed = parse_sexp_utf8(src).expect("should parse unicode atom");
        assert_eq!(sexp_to_string(&parsed), "(Id αβ_γ)");
    }

    #[test]
    fn test_parse_sexp_utf8_quoted_string_with_escapes() {
        let parsed = parse_sexp_utf8(r#"(str"a b \"c\" \\d")"#).expect("should parse");
        let Sexp::List(v) = &parsed else {
            panic!("expected list");
        };
        assert_eq!(v[1], Sexp::Atom("a b \"c\" \\d".to_string()));
        // Round-trip: serializer re-quotes.
        assert_eq!(sexp_to_string(&parsed), r#"(str "a b \"c\" \\d")"#);
    }

    #[test]
    fn test_parse_sexp_utf8_comments_skipped() {
        let parsed = parse_sexp_utf8("; header\n(a b)").expect("should skip comment");
        assert_eq!(sexp_to_string(&parsed), "(a b)");
    }
}
