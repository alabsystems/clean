// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A strict JSON reader for one NDJSON line, never through `serde_json::Value`.
//!
//! It accepts what Lean's `Lean.Json.parse` accepts at v4.36.0-rc1, with the
//! hardening upstream gave its export reader in that window, and refuses by
//! name what that reader refuses:
//!
//! - bytes after the line's one value (lean4#15542, `TrailingBytes`);
//! - an object stating a key twice, compared after unescaping (lean4#15542,
//!   lean4#15628, `DuplicateKey`);
//! - a positive exponent above 100,000 (lean4#15574, `ExponentTooLarge`).
//!
//! It is stricter than Lean's reader in two places, both refusals of input no
//! exporter writes: a `\u` escape that is not a valid surrogate pair is refused
//! (Lean substitutes U+FFFD, so two distinct escaped names could read as one),
//! and nesting deeper than [`MAX_DEPTH`] is declined rather than recursed into.
//!
//! The reader is iterative, so no input can exhaust the stack.

use hashbrown::HashSet;

use super::error::JsonError;

/// Deepest nesting of arrays and objects the reader follows. A format 3.1.0
/// record nests at most six deep; only an `mdata` payload may go further.
pub(crate) const MAX_DEPTH: usize = 512;

/// The largest positive exponent a number may carry (lean4#15574).
pub(crate) const MAX_POSITIVE_EXPONENT: u64 = 100_000;

/// The most JSON values one line may hold. A line's values are all in memory
/// at once (tens of bytes each, beside the bytes of the line), so their number
/// is bounded as the line's length is: a 128 MiB line of `0,` would otherwise
/// cost gigabytes. Format 3.1.0 records hold at most a few thousand values (the
/// Round 2026-09 archive's largest line holds 214); only an `mdata` payload
/// can hold more.
pub(crate) const MAX_VALUES_PER_LINE: usize = 1 << 20;

/// A JSON value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum JsonValue {
    /// `null`.
    Null,
    /// `true` / `false`.
    Bool(bool),
    /// A number.
    Number(JsonNumber),
    /// A string, unescaped.
    String(String),
    /// An array.
    Array(Vec<JsonValue>),
    /// An object, its entries in the order written (keys are distinct).
    Object(Vec<(String, JsonValue)>),
}

impl JsonValue {
    /// The JSON type, for a refusal message.
    pub(crate) fn type_name(&self) -> &'static str {
        match self {
            JsonValue::Null => "null",
            JsonValue::Bool(_) => "a boolean",
            JsonValue::Number(_) => "a number",
            JsonValue::String(_) => "a string",
            JsonValue::Array(_) => "an array",
            JsonValue::Object(_) => "an object",
        }
    }
}

/// A number, as written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct JsonNumber {
    /// The token.
    pub(crate) text: String,
    /// Whether the token is a natural number spelled `0|[1-9][0-9]*`: no sign,
    /// fraction or exponent.
    pub(crate) canonical_natural: bool,
}

impl JsonNumber {
    /// The value, when the token is a canonical natural that fits in `u64`.
    pub(crate) fn as_u64(&self) -> Option<u64> {
        if self.canonical_natural {
            self.text.parse::<u64>().ok()
        } else {
            None
        }
    }
}

/// Parse one line: a single JSON value, surrounded by optional whitespace.
pub(crate) fn parse_line(bytes: &[u8]) -> Result<JsonValue, JsonError> {
    if let Err(e) = std::str::from_utf8(bytes) {
        return Err(JsonError::InvalidUtf8 {
            offset: e.valid_up_to(),
        });
    }
    let mut parser = Parser {
        bytes,
        pos: 0,
        values: 0,
    };
    parser.ws();
    let value = parser.value()?;
    parser.ws();
    if parser.pos != bytes.len() {
        return Err(JsonError::TrailingBytes { offset: parser.pos });
    }
    Ok(value)
}

/// An array or object still being read.
enum Frame {
    Array(Vec<JsonValue>),
    Object {
        entries: Vec<(String, JsonValue)>,
        keys: HashSet<String>,
        key: String,
    },
}

struct Parser<'a> {
    bytes: &'a [u8],
    pos: usize,
    /// Values begun so far on this line.
    values: usize,
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.pos += 1;
        }
    }

    fn unexpected(&self, expected: &'static str) -> JsonError {
        match self.peek() {
            None => JsonError::UnexpectedEnd { offset: self.pos },
            Some(found) => JsonError::UnexpectedByte {
                offset: self.pos,
                found,
                expected,
            },
        }
    }

    fn expect_byte(&mut self, byte: u8, expected: &'static str) -> Result<(), JsonError> {
        if self.peek() == Some(byte) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.unexpected(expected))
        }
    }

    fn literal(&mut self, word: &'static [u8], value: JsonValue) -> Result<JsonValue, JsonError> {
        for &b in word {
            self.expect_byte(b, "a literal")?;
        }
        Ok(value)
    }

    /// One complete value, iteratively.
    fn value(&mut self) -> Result<JsonValue, JsonError> {
        let mut stack: Vec<Frame> = Vec::new();
        loop {
            self.ws();
            self.values += 1;
            if self.values > MAX_VALUES_PER_LINE {
                return Err(JsonError::TooManyValues {
                    offset: self.pos,
                    limit: MAX_VALUES_PER_LINE,
                });
            }
            let mut done = match self.peek() {
                Some(b'[') => {
                    self.pos += 1;
                    self.ws();
                    if self.peek() == Some(b']') {
                        self.pos += 1;
                        JsonValue::Array(Vec::new())
                    } else {
                        self.push(&mut stack, Frame::Array(Vec::new()))?;
                        continue;
                    }
                }
                Some(b'{') => {
                    self.pos += 1;
                    self.ws();
                    if self.peek() == Some(b'}') {
                        self.pos += 1;
                        JsonValue::Object(Vec::new())
                    } else {
                        let mut keys = HashSet::new();
                        let key = self.key(&mut keys)?;
                        self.push(
                            &mut stack,
                            Frame::Object {
                                entries: Vec::new(),
                                keys,
                                key,
                            },
                        )?;
                        continue;
                    }
                }
                Some(b'"') => JsonValue::String(self.string()?),
                Some(b't') => self.literal(b"true", JsonValue::Bool(true))?,
                Some(b'f') => self.literal(b"false", JsonValue::Bool(false))?,
                Some(b'n') => self.literal(b"null", JsonValue::Null)?,
                Some(b'-' | b'0'..=b'9') => JsonValue::Number(self.number()?),
                _ => return Err(self.unexpected("a JSON value")),
            };
            // Hand the finished value to the frames it completes.
            loop {
                self.ws();
                let Some(frame) = stack.last_mut() else {
                    return Ok(done);
                };
                match frame {
                    Frame::Array(items) => {
                        items.push(done);
                        match self.peek() {
                            Some(b',') => {
                                self.pos += 1;
                                break;
                            }
                            Some(b']') => {
                                self.pos += 1;
                                let Some(Frame::Array(items)) = stack.pop() else {
                                    return Err(self.unexpected("`]`"));
                                };
                                done = JsonValue::Array(items);
                            }
                            _ => return Err(self.unexpected("`,` or `]`")),
                        }
                    }
                    Frame::Object { entries, keys, key } => {
                        entries.push((std::mem::take(key), done));
                        match self.peek() {
                            Some(b',') => {
                                self.pos += 1;
                                self.ws();
                                *key = self.key(keys)?;
                                break;
                            }
                            Some(b'}') => {
                                self.pos += 1;
                                let Some(Frame::Object { entries, .. }) = stack.pop() else {
                                    return Err(self.unexpected("`}`"));
                                };
                                done = JsonValue::Object(entries);
                            }
                            _ => return Err(self.unexpected("`,` or `}`")),
                        }
                    }
                }
            }
        }
    }

    fn push(&self, stack: &mut Vec<Frame>, frame: Frame) -> Result<(), JsonError> {
        if stack.len() >= MAX_DEPTH {
            return Err(JsonError::TooDeep {
                offset: self.pos,
                limit: MAX_DEPTH,
            });
        }
        stack.push(frame);
        Ok(())
    }

    /// `"key" :`, refusing a key the object already states.
    fn key(&mut self, keys: &mut HashSet<String>) -> Result<String, JsonError> {
        let offset = self.pos;
        if self.peek() != Some(b'"') {
            return Err(self.unexpected("`\"` (an object key)"));
        }
        let key = self.string()?;
        self.ws();
        if !keys.insert(key.clone()) {
            return Err(JsonError::DuplicateKey { offset, key });
        }
        self.expect_byte(b':', "`:`")?;
        Ok(key)
    }

    fn string(&mut self) -> Result<String, JsonError> {
        self.expect_byte(b'"', "`\"`")?;
        let mut out = String::new();
        let mut start = self.pos;
        loop {
            match self.peek() {
                None => return Err(JsonError::UnexpectedEnd { offset: self.pos }),
                Some(b'"') => {
                    self.push_segment(&mut out, start)?;
                    self.pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.push_segment(&mut out, start)?;
                    let escape_at = self.pos;
                    self.pos += 1;
                    out.push(self.escape(escape_at)?);
                    start = self.pos;
                }
                Some(b) if b < 0x20 => {
                    return Err(JsonError::ControlCharacter { offset: self.pos })
                }
                Some(_) => self.pos += 1,
            }
        }
    }

    /// Append `bytes[start..pos]`, a run between ASCII delimiters of a line
    /// already checked to be UTF-8.
    fn push_segment(&self, out: &mut String, start: usize) -> Result<(), JsonError> {
        let segment = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| JsonError::InvalidUtf8 { offset: start })?;
        out.push_str(segment);
        Ok(())
    }

    fn escape(&mut self, at: usize) -> Result<char, JsonError> {
        let invalid = JsonError::InvalidEscape { offset: at };
        let Some(c) = self.peek() else {
            return Err(JsonError::UnexpectedEnd { offset: self.pos });
        };
        self.pos += 1;
        Ok(match c {
            b'"' => '"',
            b'\\' => '\\',
            b'/' => '/',
            b'b' => '\u{8}',
            b'f' => '\u{c}',
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            b'u' => {
                let first = self.hex4(at)?;
                if (0xD800..0xDC00).contains(&first) {
                    // A high surrogate must be followed by `\u` and a low one.
                    if self.peek() != Some(b'\\') {
                        return Err(invalid);
                    }
                    self.pos += 1;
                    if self.peek() != Some(b'u') {
                        return Err(invalid);
                    }
                    self.pos += 1;
                    let second = self.hex4(at)?;
                    if !(0xDC00..0xE000).contains(&second) {
                        return Err(invalid);
                    }
                    let code = 0x10000 + ((first - 0xD800) << 10) + (second - 0xDC00);
                    char::from_u32(code).ok_or(invalid)?
                } else {
                    // A lone low surrogate is no character.
                    char::from_u32(first).ok_or(invalid)?
                }
            }
            _ => return Err(invalid),
        })
    }

    fn hex4(&mut self, at: usize) -> Result<u32, JsonError> {
        let mut value = 0u32;
        for _ in 0..4 {
            let digit = self
                .peek()
                .and_then(|b| char::from(b).to_digit(16))
                .ok_or(JsonError::InvalidEscape { offset: at })?;
            self.pos += 1;
            value = value * 16 + digit;
        }
        Ok(value)
    }

    fn digits(&mut self) -> usize {
        let start = self.pos;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.pos += 1;
        }
        self.pos - start
    }

    fn number(&mut self) -> Result<JsonNumber, JsonError> {
        let start = self.pos;
        let negative = self.peek() == Some(b'-');
        if negative {
            self.pos += 1;
        }
        match self.peek() {
            Some(b'0') => self.pos += 1,
            Some(b'1'..=b'9') => {
                self.digits();
            }
            _ => return Err(self.unexpected("a digit")),
        }
        let mut plain = true;
        if self.peek() == Some(b'.') {
            plain = false;
            self.pos += 1;
            if self.digits() == 0 {
                return Err(self.unexpected("a digit"));
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            plain = false;
            self.pos += 1;
            let negative_exponent = self.peek() == Some(b'-');
            if negative_exponent || self.peek() == Some(b'+') {
                self.pos += 1;
            }
            let exp_start = self.pos;
            if self.digits() == 0 {
                return Err(self.unexpected("a digit"));
            }
            if !negative_exponent {
                // Saturating: a long run of digits is a huge exponent, not a
                // wrapped small one.
                let mut exponent = 0u64;
                for &b in &self.bytes[exp_start..self.pos] {
                    exponent = exponent
                        .saturating_mul(10)
                        .saturating_add(u64::from(b - b'0'));
                }
                if exponent > MAX_POSITIVE_EXPONENT {
                    return Err(JsonError::ExponentTooLarge { offset: start });
                }
            }
        }
        let text = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| JsonError::InvalidUtf8 { offset: start })?
            .to_owned();
        Ok(JsonNumber {
            text,
            canonical_natural: plain && !negative,
        })
    }
}
