// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive-descent parser for TrustIr text format.
//!
//! Parses the exact format produced by the Display implementations in display.rs.
//! Round-trip property: Display -> parse -> Display produces identical output.
//!
//! # Lexical grammar: the byte cursor and non-ASCII input
//!
//! The parser keeps a BYTE cursor (`Parser::pos`) into a `&str`. It moves in
//! exactly two ways, and neither can split a UTF-8 scalar or panic:
//!
//! * `bump()` consumes ONE CHARACTER: it peeks the next `char` and advances
//!   by `ch.len_utf8()`. Every single-character step goes through it, so a
//!   scanner whose predicate admits non-ASCII (comments, "anything up to the
//!   newline") is character-safe by construction.
//! * `advance(n)` consumes `n` BYTES and is FALLIBLE: a `pos + n` that is not
//!   a character boundary (or lies past the end) returns
//!   `ParseError("internal: cursor split a UTF-8 scalar at byte {pos}")` —
//!   in EVERY build profile, with no `debug_assert!`, so the release binary
//!   and the tests run the same program. It is used only after a
//!   `starts_with` of a literal, which makes the boundary hold; the internal
//!   error is the loud fail-closed signal that a caller broke that rule.
//! * a LENGTH read from the input (`bytes:<len>:<hex>`) never becomes a
//!   slice bound: the payload is consumed digit by digit through an
//!   ASCII-only test, so a declared count can neither overflow nor land a
//!   slice inside a multi-byte character. The payload is exactly
//!   `2 * len` ASCII hex digits (no sign, no whitespace), so each byte
//!   value has one spelling;
//! * a keyword-boundary lookahead (`true`, `false`, `phantomdata`) reads
//!   the next CHARACTER after the ASCII keyword, never a one-byte window.
//!
//! The scanners are defined as:
//!
//! * **plain comments** (`;` to end of line, when the first non-blank
//!   character after the `;` is not `#`): arbitrary UTF-8 up to and
//!   including the newline, served by `skip_line`. Their content is never
//!   interpreted, so an `é`, an em dash or an emoji in a comment is skipped
//!   exactly like ASCII.
//! * **directives** (`; #<word>`): the word is looked up in the ONE shared
//!   vocabulary [`crate::text_directives::TEXT_DIRECTIVES`] that the printer
//!   also spells through. An unknown word, a word in the wrong context, a
//!   `#lossy` marker (printed when [`crate::text_loss::text_losses`] is
//!   non-empty), and an unknown top-level line are each a `ParseError` —
//!   STRICT since roadmap WS4.2 (finding F-065). Until then all four were
//!   skipped, so a field the grammar could not carry (e.g. `global_asm`, and
//!   with it the `GlobalAsmNotConsumable` codegen refusal) vanished through
//!   text with no error.
//! * **bare identifiers** (`read_ident`: function/global/struct/enum symbols
//!   and the keywords the printer emits bare): the maximal run of ASCII
//!   `[A-Za-z0-9_.$]`. The alphabet is ASCII-only: a non-ASCII character
//!   (`café`, `List.mapα`, `Nat.add✝`) ends the run and the parser reports an
//!   ordinary, located `ParseError` at that character. Since the quoted-name
//!   grammar (roadmap WS4.3) the printer spells such a SYMBOL quoted
//!   (`fn @"café"(`, read by `read_symbol`), so it round-trips; the bare
//!   spelling stays a located error. Every input that parsed before still
//!   parses to the same module: a non-ASCII identifier character never
//!   parsed (it panicked), so narrowing the alphabet to ASCII loses nothing
//!   — the one deliberate exception is a signed digit pair in a `bytes:`
//!   attr (`+e`), a second spelling of a byte value that
//!   `u8::from_str_radix` used to accept and is now refused.
//! * **quoted strings** (`read_quoted_string`): arbitrary UTF-8 plus the
//!   Rust `{:?}` escapes.
//!
//! Until 2026-09-18 `advance(n)` sliced `input[pos..pos + n]` unchecked while
//! `skip_line` and `read_ident` advanced ONE BYTE per character, so a single
//! multi-byte character in a comment or a bare symbol made the parser PANIC
//! (`byte index is not a char boundary`, exit 101 from the CLI) instead of
//! returning `Err` (roadmap WS4.1, finding F-066, audit row
//! `a.format.text_parser_utf8` / skeptic c09). The standing guard is the
//! `parse_never_panics` leg of
//! `crates/trust-ir-conformance/tests/module_roundtrip_fuzz.rs` (gate 8).

use crate::constant::ConstantG;
use crate::inst::*;
use crate::level::{NoExt, TemplateRef};
use crate::node::InstrNodeG;
use crate::proof::{
    CertificateBinding, ClauseBinding, ClausePlace, ClauseSort, CleanCicKernelRecheck,
    CoverageAssurance, CoverageBound, DiagnosticSeverity, Divergence, ObligationDiagnostic,
    ObligationKind, ProofAnnotation, ProofCertificate, ProofContext, ProofDigest,
    ProofDigestAlgorithm, ProofEvidence, ProofFormula, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
    PublicObligationIdentity, SourceDefinitionRef,
};
use crate::spec::{
    ProofKind, SpecAnchor, SpecInvariant, SpecModule, SpecOrigin, SpecProof, SpecTemporal, SpecVar,
    SpecWaiver, TemporalForm,
};
use crate::text_directives as directive;
use crate::ty::{EnumDef, EnumVariant, FatPtrKind, FieldDef, FuncTyG, SetRepr, StructDef, TyG};
use crate::value::{
    BindingFrameId, BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, GlobalId, InlinedAt, ProofId,
    ProofTag, RecordId, ScopeData, SourceSpan, StructId, TyId, ValueId,
};
use crate::{
    BlockG, CallingConv, Endianness, Function, FunctionG, FunctionSummary, GlobalG, Linkage,
    Module, ModuleG, Producer, SourceBindingProvenance, SourceLoopProvenance, SourcePlace,
    SourceProvenance, TargetInfo, TlsModel,
};

/// Error returned when parsing fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub col: usize,
    pub message: String,
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "parse error at {}:{}: {}",
            self.line, self.col, self.message
        )
    }
}

impl std::error::Error for ParseError {}

type NodeComments = (
    Vec<ProofAnnotation>,
    Option<ProofContext>,
    Option<SourceSpan>,
    Option<u32>,
);

/// WS4.4: where `Parser::parse_function` is in a function's summary block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SummaryBlock {
    /// No `#summary` read yet: a clause directive is refused.
    NotStarted,
    /// Inside the block; the phase of the last directive read.
    Open(u8),
    /// The block ended (another directive followed it): any further summary
    /// directive is refused.
    Closed,
}

impl SummaryBlock {
    const HEADER: u8 = 0;
    const REQUIRES: u8 = 1;
    const ENSURES: u8 = 2;
    const DECREASES: u8 = 3;
    const BACKED_BY: u8 = 4;
    const EFFECTS: u8 = 5;

    /// The fixed-order phase of a summary-block directive word, or `None`
    /// for every other word.
    fn phase_of(word: &str) -> Option<u8> {
        match word {
            w if w == directive::SUMMARY => Some(Self::HEADER),
            w if w == directive::REQUIRES => Some(Self::REQUIRES),
            w if w == directive::ENSURES => Some(Self::ENSURES),
            w if w == directive::DECREASES => Some(Self::DECREASES),
            w if w == directive::BACKED_BY => Some(Self::BACKED_BY),
            w if w == directive::EFFECTS => Some(Self::EFFECTS),
            _ => None,
        }
    }

    fn word(phase: u8) -> &'static str {
        match phase {
            Self::HEADER => directive::SUMMARY,
            Self::REQUIRES => directive::REQUIRES,
            Self::ENSURES => directive::ENSURES,
            Self::DECREASES => directive::DECREASES,
            Self::BACKED_BY => directive::BACKED_BY,
            _ => directive::EFFECTS,
        }
    }
}

/// Internal parser state.
struct Parser<'a> {
    input: &'a str,
    pos: usize,
    line: usize,
    col: usize,
}

/// How a level's extension is spelled in text: level R spells none (`$` and
/// `?` are not type or constant syntax there, so the ordinary refusal
/// fires); level S spells `$n` (a parameter) and `?n` (a hole).
trait ParseExt: crate::level::Extension + Sized {
    fn parse_ext(p: &mut Parser<'_>) -> Option<Result<Self, ParseError>>;
    /// The level's post-parse module checks: level R refuses a vector
    /// select contract violation; a template's rules are its own (T1–T9).
    fn finish_module(module: &ModuleG<Self>) -> Result<(), String>;
}

impl ParseExt for NoExt {
    fn parse_ext(_p: &mut Parser<'_>) -> Option<Result<Self, ParseError>> {
        None
    }

    fn finish_module(module: &Module) -> Result<(), String> {
        module
            .validate_vector_select_contracts()
            .map_err(|errors| format!("{}", errors[0]))
    }
}

impl ParseExt for TemplateRef {
    fn finish_module(_module: &ModuleG<Self>) -> Result<(), String> {
        Ok(())
    }

    fn parse_ext(p: &mut Parser<'_>) -> Option<Result<Self, ParseError>> {
        let rem = p.remaining();
        let param = rem.starts_with('$');
        if !(param || rem.starts_with('?')) {
            return None;
        }
        p.bump();
        Some(p.read_u32().map(|index| {
            if param {
                TemplateRef::Param(crate::value::ParamId::new(index))
            } else {
                TemplateRef::Hole(crate::value::HoleId::new(index))
            }
        }))
    }
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn error(&self, msg: impl Into<String>) -> ParseError {
        ParseError {
            line: self.line,
            col: self.col,
            message: msg.into(),
        }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.pos..]
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn peek_char(&self) -> Option<char> {
        self.remaining().chars().next()
    }

    /// Account one consumed character in the line/column bookkeeping.
    fn account(&mut self, ch: char) {
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
    }

    /// Consume ONE CHARACTER: peek it and advance the byte cursor by
    /// `ch.len_utf8()`. Cannot split a UTF-8 scalar, so every
    /// single-character step of every scanner goes through here.
    fn bump(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.account(ch);
        self.pos += ch.len_utf8();
        Some(ch)
    }

    /// Consume `s`, which the caller has just matched with
    /// `self.remaining().starts_with(s)`. Walks `s` by character through
    /// `bump`, so it is char-safe by construction and cannot fail. (No
    /// `debug_assert!` here either: debug and release run the same program.)
    fn bump_matched(&mut self, s: &str) {
        for _ in s.chars() {
            self.bump();
        }
    }

    /// Advance the BYTE cursor by `n`. FALLIBLE: a `pos + n` that is not a
    /// UTF-8 character boundary (or lies past the end of the input) is
    /// refused with an `internal: cursor split` `ParseError` and leaves the
    /// cursor where it was. This is deliberately NOT a `debug_assert!`: debug
    /// and release builds behave identically, so the "never panics" property
    /// the tests check is the property that ships (roadmap WS4.1). Callers
    /// use it only after a `starts_with` of a literal; single characters go
    /// through `bump`.
    fn advance(&mut self, n: usize) -> Result<(), ParseError> {
        let Some(end) = self
            .pos
            .checked_add(n)
            .filter(|&end| self.input.is_char_boundary(end))
        else {
            return Err(self.error(format!(
                "internal: cursor split a UTF-8 scalar at byte {}",
                self.pos
            )));
        };
        for ch in self.input[self.pos..end].chars() {
            self.account(ch);
        }
        self.pos = end;
        Ok(())
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_whitespace() {
                self.bump();
            } else {
                break;
            }
        }
    }

    /// The optional indirect-call ABI suffix ` cc=<conv>` of `call_indirect`
    /// and `invoke_indirect` (the C convention when absent).
    fn parse_indirect_calling_conv(&mut self) -> Result<CallingConv, ParseError> {
        self.skip_whitespace_no_newline();
        if !self.remaining().starts_with("cc=") {
            return Ok(CallingConv::default());
        }
        self.advance(3)?;
        let tok = self.read_ident()?;
        Ok(match tok.as_str() {
            "ccc" => CallingConv::C,
            "fastcc" => CallingConv::Fast,
            "coldcc" => CallingConv::Cold,
            "rustcc" => CallingConv::Rust,
            "swiftcc" => CallingConv::Swift,
            other => match CallingConv::ALL
                .into_iter()
                .find(|c| c.to_string() == other)
            {
                Some(conv) => conv,
                None => {
                    return Err(self.error(format!("unknown calling convention: '{other}'")));
                }
            },
        })
    }

    fn skip_whitespace_no_newline(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch == ' ' || ch == '\t' {
                self.bump();
            } else {
                break;
            }
        }
    }

    /// Skip to and past the next newline. Comment bodies and unknown lines
    /// are arbitrary UTF-8, so the cursor moves one CHARACTER at a time
    /// (`bump`). It returns `Result` although `bump` cannot fail so that the
    /// site stays on the fallible-cursor contract: a byte step reintroduced
    /// here (`self.advance(1)?`) surfaces as the named `internal: cursor
    /// split` refusal the gate-8 `parse_never_panics` leg fails on, not as a
    /// silent early return that the callers' line loops would spin on.
    fn skip_line(&mut self) -> Result<(), ParseError> {
        while let Some(ch) = self.bump() {
            if ch == '\n' {
                break;
            }
        }
        Ok(())
    }

    /// True iff the cursor sits on a `;` comment whose first non-blank
    /// character is `#` — a DIRECTIVE, which is either in the shared
    /// vocabulary ([`crate::text_directives::TEXT_DIRECTIVES`]) or refused.
    fn at_directive(&self) -> bool {
        self.remaining()
            .strip_prefix(';')
            .is_some_and(|rest| rest.trim_start_matches([' ', '\t']).starts_with('#'))
    }

    /// Read a directive word after its `;` has been consumed (roadmap
    /// WS4.2). A plain comment (`;` not followed, after blanks, by `#`)
    /// returns `Ok(None)` with the cursor on its first non-blank character.
    /// A `#<word>` returns the matching [`crate::text_directives`] constant.
    ///
    /// # Errors
    ///
    /// * `#lossy` — the text was printed from a module with fields the
    ///   grammar cannot carry, and parsing it back would silently drop them;
    /// * any word not in the table — `unknown directive `#<word>` — refusing
    ///   rather than dropping it` (a newer printer's field, a typo, or a
    ///   printer-only directive). Until WS4.2 both were skipped.
    fn read_directive_word(&mut self) -> Result<Option<&'static str>, ParseError> {
        use crate::text_directives::{LOSSY, TEXT_DIRECTIVES, is_directive_word_char};
        self.skip_whitespace_no_newline();
        if self.peek_char() != Some('#') {
            return Ok(None);
        }
        let start = self.pos;
        self.bump();
        while self.peek_char().is_some_and(is_directive_word_char) {
            self.bump();
        }
        let word = &self.input[start..self.pos];
        if word == LOSSY {
            let rest = self.remaining();
            let summary = rest[..rest.find('\n').unwrap_or(rest.len())]
                .trim_start_matches(':')
                .trim();
            return Err(self.error(format!(
                "this text was printed LOSSILY ({summary}); it cannot be parsed back \
                 — re-emit from the binary/serde artifact"
            )));
        }
        match TEXT_DIRECTIVES.iter().find(|known| **known == word) {
            Some(known) => Ok(Some(known)),
            None => Err(self.error(format!(
                "unknown directive `{word}` — refusing rather than dropping it"
            ))),
        }
    }

    /// Consume one `;` comment line at MODULE level (the header or between
    /// top-level items): a plain comment is skipped; no directive is valid
    /// here, so a `#lossy` or any other `#<word>` is refused.
    fn skip_module_comment(&mut self) -> Result<(), ParseError> {
        self.bump(); // the `;`
        match self.read_directive_word()? {
            None => self.skip_line(),
            Some(word) => Err(self.error(format!(
                "directive `{word}` is not valid at module level — refusing rather than \
                 dropping it"
            ))),
        }
    }

    fn expect_str(&mut self, s: &str) -> Result<(), ParseError> {
        self.skip_whitespace();
        if self.remaining().starts_with(s) {
            self.advance(s.len())?;
            Ok(())
        } else {
            let got: String = self.remaining().chars().take(s.len() + 10).collect();
            Err(self.error(format!("expected '{}', got '{}'", s, got)))
        }
    }

    fn consume_keyword(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        if !self.remaining().starts_with(s) {
            return false;
        }
        let end = self.pos + s.len();
        let boundary = self.input[end..]
            .chars()
            .next()
            .is_none_or(|ch| ch.is_ascii_whitespace() || matches!(ch, '"' | '[' | '{' | '('));
        if boundary {
            self.bump_matched(s);
            true
        } else {
            false
        }
    }

    /// One hex digit (0-9a-fA-F) -> its value. Serves v25 `Bytes` constants
    /// and `bytes:` dialect attrs; the ASCII-only test precedes the advance.
    fn expect_hex_digit(&mut self) -> Result<u8, ParseError> {
        match self.peek_char() {
            Some(c) if c.is_ascii_hexdigit() => {
                self.bump();
                Ok(c.to_digit(16).expect("hexdigit checked") as u8)
            }
            other => Err(self.error(format!("expected hex digit, got {other:?}"))),
        }
    }

    /// A blob digest: exactly 64 hex digits (32 bytes), no separator. Serves
    /// v70 `tensor_blob<..>` constants and `blob` module rows.
    fn read_blob_digest(&mut self) -> Result<crate::blob::BlobDigest, ParseError> {
        let mut digest = [0u8; 32];
        for byte in &mut digest {
            let hi = self.expect_hex_digit()?;
            let lo = self.expect_hex_digit()?;
            *byte = (hi << 4) | lo;
        }
        if self.peek_char().is_some_and(|c| c.is_ascii_hexdigit()) {
            return Err(self.error("a blob digest is exactly 64 hex digits".to_string()));
        }
        Ok(crate::blob::BlobDigest(digest))
    }

    fn expect_char(&mut self, ch: char) -> Result<(), ParseError> {
        self.skip_whitespace();
        match self.peek_char() {
            Some(c) if c == ch => {
                self.bump();
                Ok(())
            }
            Some(c) => Err(self.error(format!("expected '{}', got '{}'", ch, c))),
            None => Err(self.error(format!("expected '{}', got EOF", ch))),
        }
    }

    /// Try to consume a string; return true if consumed, false if not.
    fn try_str(&mut self, s: &str) -> bool {
        let saved_pos = self.pos;
        let saved_line = self.line;
        let saved_col = self.col;
        self.skip_whitespace();
        if self.remaining().starts_with(s) {
            self.bump_matched(s);
            true
        } else {
            self.pos = saved_pos;
            self.line = saved_line;
            self.col = saved_col;
            false
        }
    }

    /// Read an identifier: the maximal run of ASCII `[A-Za-z0-9_.$]` — see
    /// the module doc's lexical-grammar section. A non-ASCII character ends
    /// the run, so a BARE symbol such as `café` is a located `ParseError` at
    /// the `é`; the printer spells it quoted (`read_symbol`, roadmap WS4.3).
    fn read_ident(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            // `$` is admitted so linker-symbol spellings round-trip through the
            // text codec: Darwin symbol variants (`opendir$INODE64`), TLV init
            // templates (`X$tlv$init`), and legacy-mangled Rust symbols
            // (`_$LT$`, `$u20$`). It is never a syntactic token in this format, so
            // widening the identifier set here cannot change any existing parse.
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '.' || ch == '$' {
                // ASCII-only (roadmap WS4.1). The alphabet used to be the
                // Unicode `is_alphanumeric` while the cursor stepped ONE BYTE,
                // so `café` split the `é` and panicked (F-066).
                self.bump();
            } else {
                break;
            }
        }
        if self.pos == start {
            Err(self.error("expected identifier"))
        } else {
            Ok(self.input[start..self.pos].to_string())
        }
    }

    /// Read the strictly ASCII alphabet of a nominal dialect identity.
    /// Reject non-ASCII before advancing the byte cursor.
    fn read_dialect_type_name(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while self
            .peek_char()
            .is_some_and(crate::dialect::inst::is_valid_dialect_name_char)
        {
            self.bump();
        }
        if self.pos == start {
            Err(self.error("expected nonempty ASCII dialect type name"))
        } else {
            Ok(self.input[start..self.pos].to_string())
        }
    }

    /// WS4.3: read a definition-site SYMBOL — the bare-identifier alphabet, or
    /// a quoted, escaped string for every name outside it.
    ///
    /// WHY. `read_ident`'s alphabet is `[A-Za-z0-9_.$]`, so a producer minting a
    /// name outside it made its whole module UNREPRESENTABLE in text
    /// (`TextLoss::UnspellableName` — the module is refused, not just the name).
    /// Measured 2026-09-21 over the `trustc-ir` battery lane: 98 of 152 text
    /// losses were exactly this, from names like
    /// `m::wsum::<shadowed-by-clean-origin:FuncId(4)>`. Text-representability
    /// was a property of which characters a producer happened to pick.
    ///
    /// ONE SPELLING PER CONSTRUCT (SPEC §3). A name inside the bare alphabet
    /// MUST be spelled bare: the quoted spelling of such a name is REFUSED, so
    /// parsing stays a bijection on printer output and no second text can denote
    /// the same module. Bare and quoted therefore denote disjoint name sets.
    ///
    /// Accepting a quote here is additive: `read_ident` errors on `"` today, so
    /// no previously-valid text changes meaning.
    fn read_symbol(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        if self.peek_char() != Some('"') {
            return self.read_ident();
        }
        let name = self.read_quoted_string()?;
        if name.is_empty() {
            return Err(self.error("empty symbol"));
        }
        if crate::text_loss::is_bare_ident(&name) {
            return Err(self.error(
                &format!("name `{name}` is in the bare alphabet and must be spelled bare")[..],
            ));
        }
        Ok(name)
    }

    /// Read a quoted string (as produced by Rust's {:?} for strings).
    fn read_quoted_string(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        self.expect_char('"')?;
        let mut result = String::new();
        loop {
            match self.peek_char() {
                None => return Err(self.error("unterminated string")),
                Some('"') => {
                    self.bump();
                    return Ok(result);
                }
                Some('\\') => {
                    self.bump();
                    match self.peek_char() {
                        Some('"') => {
                            self.bump();
                            result.push('"');
                        }
                        Some('\\') => {
                            self.bump();
                            result.push('\\');
                        }
                        Some('n') => {
                            self.bump();
                            result.push('\n');
                        }
                        Some('t') => {
                            self.bump();
                            result.push('\t');
                        }
                        // Full control-char escape decoding (finding F): `\r`,
                        // `\0`, and `\u{HEX}` for any other control character.
                        Some('r') => {
                            self.bump();
                            result.push('\r');
                        }
                        Some('0') => {
                            self.bump();
                            result.push('\0');
                        }
                        Some('u') => {
                            self.bump();
                            self.expect_char('{')?;
                            let start = self.pos;
                            while let Some(ch) = self.peek_char() {
                                if ch.is_ascii_hexdigit() {
                                    self.bump();
                                } else {
                                    break;
                                }
                            }
                            let hex = self.input[start..self.pos].to_string();
                            self.expect_char('}')?;
                            let code = u32::from_str_radix(&hex, 16).map_err(|_| {
                                self.error(format!("invalid \\u escape: '{}'", hex))
                            })?;
                            let ch = char::from_u32(code).ok_or_else(|| {
                                self.error(format!("invalid unicode scalar: {:#x}", code))
                            })?;
                            result.push(ch);
                        }
                        Some(c) => {
                            self.bump();
                            result.push(c);
                        }
                        None => return Err(self.error("unterminated escape")),
                    }
                }
                Some(ch) => {
                    self.bump();
                    result.push(ch);
                }
            }
        }
    }

    /// Parse the exact quoted representation emitted by [`ProofDigest`], for
    /// example `"sha256:0123..."`. Source-provenance digests are kept as one
    /// token so their algorithm and fixed width cannot be separated by a
    /// comment or ambiguous whitespace.
    fn read_source_provenance_digest(&mut self) -> Result<ProofDigest, ParseError> {
        let encoded = self.read_quoted_string()?;
        let Some((algorithm, hex)) = encoded.split_once(':') else {
            return Err(self.error("source-provenance digest must contain an algorithm prefix"));
        };
        let algorithm = match algorithm {
            "sha256" => ProofDigestAlgorithm::Sha256,
            "trust_ir-stable-v1" => ProofDigestAlgorithm::TrustIrStableV1,
            other => {
                return Err(self.error(format!(
                    "unknown source-provenance digest algorithm: '{other}'"
                )));
            }
        };
        if hex.len() != 64 || !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(
                self.error("source-provenance digest must contain exactly 64 hexadecimal digits")
            );
        }
        let mut bytes = [0_u8; 32];
        for (index, byte) in bytes.iter_mut().enumerate() {
            let start = index * 2;
            *byte = u8::from_str_radix(&hex[start..start + 2], 16)
                .map_err(|_| self.error("invalid source-provenance digest hex"))?;
        }
        Ok(ProofDigest { algorithm, bytes })
    }

    /// Read a u32 integer.
    fn read_u32(&mut self) -> Result<u32, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(self.error("expected integer"));
        }
        let s = &self.input[start..self.pos];
        s.parse::<u32>()
            .map_err(|_| self.error(format!("invalid u32: '{}'", s)))
    }

    /// Read a u64 integer.
    fn read_u64(&mut self) -> Result<u64, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(self.error("expected integer"));
        }
        let s = &self.input[start..self.pos];
        s.parse::<u64>()
            .map_err(|_| self.error(format!("invalid u64: '{}'", s)))
    }

    /// Read a signed 64-bit integer (optional leading `-`).
    fn read_i64(&mut self) -> Result<i64, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        if self.peek_char() == Some('-') {
            self.bump();
        }
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        let s = &self.input[start..self.pos];
        if s.is_empty() || s == "-" {
            return Err(self.error("expected signed integer"));
        }
        s.parse::<i64>()
            .map_err(|_| self.error(format!("invalid i64: '{}'", s)))
    }

    /// Read a signed 128-bit integer (optional leading `-`).
    fn read_i128(&mut self) -> Result<i128, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        if self.peek_char() == Some('-') {
            self.bump();
        }
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        let s = &self.input[start..self.pos];
        if s.is_empty() || s == "-" {
            return Err(self.error("expected signed integer"));
        }
        s.parse::<i128>()
            .map_err(|_| self.error(format!("invalid i128: '{}'", s)))
    }

    /// Read an unsigned 128-bit integer.
    fn read_u128(&mut self) -> Result<u128, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        let s = &self.input[start..self.pos];
        if s.is_empty() {
            return Err(self.error("expected unsigned integer"));
        }
        s.parse::<u128>()
            .map_err(|_| self.error(format!("invalid u128: '{}'", s)))
    }

    /// Read a value reference: %N
    /// The optional `, KIND` and `, panic @func.E at LOC` clauses of an
    /// `assert` / `assert_invoke` after its condition (plan item P: wire v52
    /// kinds, amendment P: wire v54 sites). Each clause must start on the
    /// instruction's own line with ", ". `unspecified` is never written: the
    /// kindless spelling is the ONE spelling of an `Unspecified` assert.
    fn parse_assert_kind_and_site(
        &mut self,
    ) -> Result<(crate::inst::AssertKind, Option<crate::inst::PanicSite>), ParseError> {
        let mut kind = crate::inst::AssertKind::Unspecified;
        if !self.remaining().starts_with(", ") {
            return Ok((kind, None));
        }
        self.expect_char(',')?;
        let mut keyword = self.read_ident()?;
        if keyword != "panic" {
            kind = match keyword.as_str() {
                "overflow" => {
                    let op = self.read_ident()?;
                    crate::inst::AssertKind::Overflow(
                        crate::inst::AssertOverflowOp::from_name(&op).ok_or_else(|| {
                            self.error(format!("unknown assert overflow op `{op}`"))
                        })?,
                    )
                }
                "div_by_zero" => crate::inst::AssertKind::DivByZero,
                "rem_by_zero" => crate::inst::AssertKind::RemByZero,
                "null_ptr" => crate::inst::AssertKind::NullPtr,
                "bounds_check" => {
                    let index = self.read_value_id()?;
                    self.expect_char(',')?;
                    let len = self.read_value_id()?;
                    crate::inst::AssertKind::BoundsCheck { index, len }
                }
                "misaligned_ptr" => {
                    let required = self.read_value_id()?;
                    self.expect_char(',')?;
                    let found = self.read_value_id()?;
                    crate::inst::AssertKind::MisalignedPtr { required, found }
                }
                other => return Err(self.error(format!("unknown assert kind `{other}`"))),
            };
            if !self.remaining().starts_with(", ") {
                return Ok((kind, None));
            }
            self.expect_char(',')?;
            keyword = self.read_ident()?;
            if keyword != "panic" {
                return Err(self.error(format!(
                    "expected the assert's `panic @func.N at ..` clause, got `{keyword}`"
                )));
            }
        }
        // `panic @func.E at @global.G` | `panic @func.E at %V`
        self.skip_whitespace_no_newline();
        self.expect_str("@func.")?;
        let entry = FuncId::new(self.read_u32()?);
        self.skip_whitespace_no_newline();
        self.expect_str("at ")?;
        self.skip_whitespace_no_newline();
        let location = if self.remaining().starts_with("@global.") {
            self.advance(8)?;
            crate::inst::PanicLocation::Global(crate::value::GlobalId::new(self.read_u32()?))
        } else {
            crate::inst::PanicLocation::Value(self.read_value_id()?)
        };
        Ok((kind, Some(crate::inst::PanicSite { entry, location })))
    }

    fn read_value_id(&mut self) -> Result<ValueId, ParseError> {
        self.skip_whitespace();
        self.expect_char('%')?;
        let n = self.read_u32()?;
        Ok(ValueId::new(n))
    }

    /// Read a block reference: bbN
    fn read_block_id(&mut self) -> Result<BlockId, ParseError> {
        self.skip_whitespace();
        self.expect_str("bb")?;
        let n = self.read_u32()?;
        Ok(BlockId::new(n))
    }

    /// Read optional block arguments: (v1, v2, ...)
    fn read_block_args(&mut self) -> Result<Vec<ValueId>, ParseError> {
        if self.try_str("(") {
            let mut args = Vec::new();
            if !self.try_str(")") {
                args.push(self.read_value_id()?);
                while self.try_str(",") {
                    args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            Ok(args)
        } else {
            Ok(Vec::new())
        }
    }

    /// Read a `tensor_contract` axis-pair list (PKG-U13a): `[a:b, c:d]`, each
    /// pair `lhs axis:rhs axis` as two u32s; the empty list is `[]`. A pair
    /// missing either axis or its `:`, a trailing `,`, or an unclosed list is
    /// a `ParseError`. The printer is `display::write_axis_pairs`.
    fn read_axis_pairs(&mut self) -> Result<Vec<(u32, u32)>, ParseError> {
        self.expect_char('[')?;
        let mut pairs = Vec::new();
        if self.try_str("]") {
            return Ok(pairs);
        }
        loop {
            let lhs_axis = self.read_u32()?;
            self.expect_char(':')?;
            let rhs_axis = self.read_u32()?;
            pairs.push((lhs_axis, rhs_axis));
            if !self.try_str(",") {
                break;
            }
        }
        self.expect_char(']')?;
        Ok(pairs)
    }

    /// Read a bracketed, comma-separated list of `item`s (PKG-U13c): `[a, b]`,
    /// the empty list `[]`. A trailing `,` or an unclosed list is a
    /// `ParseError`.
    fn read_bracketed<T>(
        &mut self,
        mut item: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        self.expect_char('[')?;
        let mut items = Vec::new();
        if self.try_str("]") {
            return Ok(items);
        }
        loop {
            items.push(item(self)?);
            if !self.try_str(",") {
                break;
            }
        }
        self.expect_char(']')?;
        Ok(items)
    }

    /// Read a tensor map lane or a tensor view node reference: `$N`.
    fn read_lane(&mut self) -> Result<u32, ParseError> {
        self.expect_char('$')?;
        self.read_u32()
    }

    /// Read one tensor map node (PKG-U13c): the scalar instruction's own
    /// spelling with `$lane` for `%value` (`add i32 $0, $1`, `neg i32 $0`,
    /// `icmp slt i32 $0, $1`, `select i32 $2, $0, $1`, `sext i8 $0 to i32`).
    /// The printer is `TensorMapNode`'s `Display`.
    fn parse_tensor_map_node<X: ParseExt>(
        &mut self,
    ) -> Result<crate::TensorMapNode<X>, ParseError> {
        use crate::TensorMapNode as N;
        let name = self.read_ident()?;
        if name == "icmp" {
            let op_name = self.read_ident()?;
            let op = Self::parse_icmpop(&op_name)
                .ok_or_else(|| self.error(format!("unknown icmp op: '{op_name}'")))?;
            let ty = self.parse_ty()?;
            let lhs = self.read_lane()?;
            self.expect_char(',')?;
            let rhs = self.read_lane()?;
            return Ok(N::ICmp { op, ty, lhs, rhs });
        }
        if name == "select" {
            let ty = self.parse_ty()?;
            let cond = self.read_lane()?;
            self.expect_char(',')?;
            let then_lane = self.read_lane()?;
            self.expect_char(',')?;
            let else_lane = self.read_lane()?;
            return Ok(N::Select {
                ty,
                cond,
                then_lane,
                else_lane,
            });
        }
        if let Some(op) = Self::parse_binop(&name) {
            let ty = self.parse_ty()?;
            let lhs = self.read_lane()?;
            self.expect_char(',')?;
            let rhs = self.read_lane()?;
            return Ok(N::BinOp { op, ty, lhs, rhs });
        }
        if let Some(op) = Self::parse_unop(&name) {
            let ty = self.parse_ty()?;
            let operand = self.read_lane()?;
            return Ok(N::UnOp { op, ty, operand });
        }
        if let Some(op) = Self::parse_castop(&name) {
            let src_ty = self.parse_ty()?;
            let operand = self.read_lane()?;
            self.expect_str("to")?;
            let dst_ty = self.parse_ty()?;
            return Ok(N::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            });
        }
        Err(self.error(format!("unknown tensor map node: '{name}'")))
    }

    /// Read one tensor view node (PKG-U13c): `lit(N)`, `param(K)`,
    /// `src_extent(J)`, `coord(I)`, or `OP($a, $b)` for `OP` in `add sub mul
    /// div rem min max`. The printer is `TensorIndexExpr`'s `Display`.
    fn parse_tensor_index_expr(&mut self) -> Result<crate::TensorIndexExpr, ParseError> {
        use crate::TensorIndexExpr as E;
        let name = self.read_ident()?;
        self.expect_char('(')?;
        let expr = match name.as_str() {
            "lit" => E::Lit(self.read_u64()?),
            "param" => E::Param(self.read_u32()?),
            "src_extent" => E::SrcExtent(self.read_u32()?),
            "coord" => E::Coord(self.read_u32()?),
            "add" | "sub" | "mul" | "div" | "rem" | "min" | "max" => {
                let a = self.read_lane()?;
                self.expect_char(',')?;
                let b = self.read_lane()?;
                match name.as_str() {
                    "add" => E::Add(a, b),
                    "sub" => E::Sub(a, b),
                    "mul" => E::Mul(a, b),
                    "div" => E::Div(a, b),
                    "rem" => E::Rem(a, b),
                    "min" => E::Min(a, b),
                    _ => E::Max(a, b),
                }
            }
            _ => return Err(self.error(format!("unknown tensor view node: '{name}'"))),
        };
        self.expect_char(')')?;
        Ok(expr)
    }

    /// Try to parse ", align N" suffix. Returns Ok(Some(n)) if present.
    fn try_parse_align(&mut self) -> Result<Option<u64>, ParseError> {
        let saved_pos = self.pos;
        let saved_line = self.line;
        let saved_col = self.col;
        if self.try_str(",") {
            self.skip_whitespace_no_newline();
            if self.remaining().starts_with("align ") {
                self.advance(6)?;
                let n = self.read_u64()?;
                return Ok(Some(n));
            }
            // Not align -- restore position (we consumed the comma)
            self.pos = saved_pos;
            self.line = saved_line;
            self.col = saved_col;
        }
        Ok(None)
    }

    /// Try to parse a linkage keyword. Returns default (External) if none found.
    fn try_parse_linkage(&mut self) -> Result<Linkage, ParseError> {
        self.skip_whitespace();
        let rem = self.remaining();
        // v41 linkages FIRST. The space-delimited prefixes below do not
        // actually shadow them (`weak_odr ` is not `weak `), but longest-first
        // is the house convention and survives a future non-delimited token.
        Ok(if rem.starts_with("available_externally ") {
            self.advance(21)?;
            Linkage::AvailableExternally
        } else if rem.starts_with("external_weak ") {
            self.advance(14)?;
            Linkage::ExternalWeak
        } else if rem.starts_with("weak_odr ") {
            self.advance(9)?;
            Linkage::WeakOdr
        } else if rem.starts_with("linkonce_odr ") {
            self.advance(13)?;
            Linkage::LinkOnceOdr
        } else if rem.starts_with("internal ") {
            self.advance(9)?;
            Linkage::Internal
        } else if rem.starts_with("private ") {
            self.advance(8)?;
            Linkage::Private
        } else if rem.starts_with("weak ") {
            self.advance(5)?;
            Linkage::Weak
        } else if rem.starts_with("linkonce ") {
            self.advance(9)?;
            Linkage::LinkOnce
        } else if rem.starts_with("external ") {
            self.advance(9)?;
            Linkage::External
        } else {
            Linkage::External
        })
    }

    /// Try to parse global TLS metadata: tls(<model>).
    fn try_parse_tls_model(&mut self) -> Result<Option<TlsModel>, ParseError> {
        self.skip_whitespace();
        if !self.remaining().starts_with("tls(") {
            return Ok(None);
        }
        self.advance(3)?;
        self.expect_char('(')?;
        let model = self.read_ident()?;
        self.expect_char(')')?;
        let tls = match model.as_str() {
            "local_exec" => TlsModel::LocalExec,
            "initial_exec" => TlsModel::InitialExec,
            "general_dynamic" => TlsModel::GeneralDynamic,
            "local_dynamic" => TlsModel::LocalDynamic,
            other => return Err(self.error(format!("unknown TLS model: '{}'", other))),
        };
        Ok(Some(tls))
    }

    /// Try to parse a calling convention keyword. Returns default (C) if none found.
    fn try_parse_calling_conv(&mut self) -> Result<CallingConv, ParseError> {
        self.skip_whitespace();
        // v45 conventions (WS3.12): resolved through `CallingConv::ALL` and
        // its `Display`, so the printer and parser share one spelling.
        for conv in CallingConv::ALL.into_iter().filter(|c| c.is_abi_surface()) {
            let token = format!("{conv} ");
            if self.remaining().starts_with(token.as_str()) {
                self.advance(token.len())?;
                return Ok(conv);
            }
        }
        let rem = self.remaining();
        Ok(if rem.starts_with("fastcc ") {
            self.advance(7)?;
            CallingConv::Fast
        } else if rem.starts_with("coldcc ") {
            self.advance(7)?;
            CallingConv::Cold
        } else if rem.starts_with("rustcc ") {
            self.advance(7)?;
            CallingConv::Rust
        } else if rem.starts_with("swiftcc ") {
            self.advance(8)?;
            CallingConv::Swift
        } else if rem.starts_with("ccc ") {
            self.advance(4)?;
            CallingConv::C
        } else {
            CallingConv::C
        })
    }

    /// Parse a type.
    fn parse_ty<X: ParseExt>(&mut self) -> Result<TyG<X>, ParseError> {
        self.skip_whitespace();
        // Amendment S: a template's `$n` / `?n`; the level-R parser spells none.
        if let Some(ext) = X::parse_ext(self) {
            return ext.map(TyG::Ext);
        }
        let rem = self.remaining();

        // Reference types
        if rem.starts_with("&mut ") {
            self.advance(5)?; // "&mut "
            let inner = self.parse_ty()?;
            return Ok(TyG::RefMut(Box::new(inner)));
        }
        if rem.starts_with('&') && !rem.starts_with("&&") {
            // Simple &T (not &&T which would be &(&T))
            self.bump();
            let inner = self.parse_ty()?;
            return Ok(TyG::Ref(Box::new(inner)));
        }
        if rem.starts_with("&&") {
            // &&T = &(&T)
            self.bump(); // consume first &
            let inner = self.parse_ty()?;
            return Ok(TyG::Ref(Box::new(inner)));
        }
        if rem.starts_with("*const ") {
            self.advance(7)?;
            let inner = self.parse_ty()?;
            return Ok(TyG::PtrConst(Box::new(inner)));
        }
        if rem.starts_with("*mut ") {
            self.advance(5)?;
            let inner = self.parse_ty()?;
            return Ok(TyG::PtrMut(Box::new(inner)));
        }
        if rem.starts_with("Rc<") {
            self.advance(3)?;
            let inner = self.parse_ty()?;
            self.expect_char('>')?;
            return Ok(TyG::Rc(Box::new(inner)));
        }
        if rem.starts_with('!') {
            self.bump();
            return Ok(TyG::Never);
        }

        // Fat pointer: fatptr<str> | fatptr<slice ty.N> | fatptr<dyn.N>
        //            | fatptr<container_len> | fatptr<container_vtable>
        if rem.starts_with("fatptr<") {
            self.advance(7)?;
            if self.try_str("str") {
                self.expect_char('>')?;
                return Ok(TyG::FatPtr(FatPtrKind::Str));
            }
            if self.try_str("slice") {
                self.expect_str("ty.")?;
                let elem_id = self.read_u32()?;
                self.expect_char('>')?;
                return Ok(TyG::FatPtr(FatPtrKind::Slice(TyId::new(elem_id))));
            }
            // v38. Must be tried before the `dyn.` fallthrough, and it cannot
            // collide with the `str` arm above: `try_str("str")` does not match
            // "container_len".
            if self.try_str("container_len") {
                self.expect_char('>')?;
                return Ok(TyG::FatPtr(FatPtrKind::ContainerLen));
            }
            // v40. The `dyn`-tail sibling, likewise ahead of the `dyn.`
            // fallthrough. The two `container_` spellings cannot shadow each
            // other: `try_str` matches the whole keyword and they diverge at
            // `container_l` / `container_v`.
            if self.try_str("container_vtable") {
                self.expect_char('>')?;
                return Ok(TyG::FatPtr(FatPtrKind::ContainerVtable));
            }
            self.expect_str("dyn.")?;
            let trait_id = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(TyG::FatPtr(FatPtrKind::TraitObject { trait_id }));
        }

        // Set: set<ty.N, bitset|boxed>
        if rem.starts_with("set<") {
            self.advance(4)?;
            self.expect_str("ty.")?;
            let elem_id = self.read_u32()?;
            self.expect_str(",")?;
            self.skip_whitespace();
            let repr_ident = self.read_ident()?;
            let repr = match repr_ident.as_str() {
                "bitset" => SetRepr::Bitset,
                "boxed" => SetRepr::Boxed,
                other => return Err(self.error(format!("unknown set repr: '{}'", other))),
            };
            self.expect_char('>')?;
            return Ok(TyG::Set(TyId::new(elem_id), repr));
        }

        // Sequence: seq<ty.N>
        if rem.starts_with("seq<") {
            self.advance(4)?;
            self.expect_str("ty.")?;
            let elem_id = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(TyG::Sequence(TyId::new(elem_id)));
        }

        // Fixed-width vector: <N x Ty>
        if rem.starts_with('<') {
            self.bump();
            let lanes = self.read_u32()?;
            if lanes == 0 {
                return Err(self.error("vector lane count must be nonzero"));
            }
            self.expect_str("x")?;
            let elem = self.parse_ty()?;
            self.expect_char('>')?;
            return Ok(TyG::Vector(Box::new(elem), lanes));
        }

        // Unit `()`, zero-element tuple `(,)`, or tuple `(T, ...)`.
        if rem.starts_with('(') {
            self.bump();
            self.skip_whitespace();
            if self.try_str(")") {
                // `()` is the unit type, distinct from the empty tuple.
                return Ok(TyG::Unit);
            }
            if self.try_str(",") {
                // `(,)` is the zero-element tuple.
                self.skip_whitespace();
                self.expect_char(')')?;
                return Ok(TyG::Tuple(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_ty()?);
            while self.try_str(",") {
                elems.push(self.parse_ty()?);
            }
            self.expect_char(')')?;
            return Ok(TyG::Tuple(elems));
        }

        // Array: [ty.N x M]
        if rem.starts_with('[') {
            self.bump();
            self.expect_str("ty.")?;
            let elem_id = self.read_u32()?;
            self.expect_str("x")?;
            let len = self.read_u64()?;
            self.expect_char(']')?;
            return Ok(TyG::Array(TyId::new(elem_id), len));
        }

        // Refinement: refine<ty.N, pred.M> (v30 typed value model).
        if rem.starts_with("refine<") {
            self.advance(7)?;
            self.expect_str("ty.")?;
            let base = self.read_u32()?;
            self.expect_char(',')?;
            self.expect_str("pred.")?;
            let pred = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(TyG::Refine(
                TyId::new(base),
                crate::value::PredId::new(pred),
            ));
        }

        // Nominal dialect type: dialect<namespace, name, version>.
        if rem.starts_with("dialect<") {
            self.advance(8)?;
            let namespace = self.read_dialect_type_name()?;
            self.expect_char(',')?;
            let name = self.read_dialect_type_name()?;
            self.expect_char(',')?;
            let version = self.read_u32()?;
            self.expect_char('>')?;
            let ty = crate::DialectTy::new(namespace, name, version);
            ty.validate()
                .map_err(|error| self.error(error.to_string()))?;
            return Ok(TyG::Dialect(Box::new(ty)));
        }

        if rem.starts_with("storage<") {
            self.advance(8)?;
            let size = self.read_u64()?;
            self.expect_char(',')?;
            let align = self.read_u64()?;
            self.expect_char('>')?;
            let layout = crate::StorageLayout::new(size, align);
            if !layout.is_well_formed(64) {
                return Err(self.error("invalid storage-only layout geometry"));
            }
            return Ok(TyG::Storage(layout));
        }

        // v43 nominal opaque runtime handle: handle<"name", "runtime::path">.
        // Both halves are quoted (the runtime path carries `::`); the
        // charset is re-checked by `HandleTy::validate` after decoding.
        if rem.starts_with("handle<") {
            self.advance(7)?;
            let name = self.read_quoted_string()?;
            self.expect_char(',')?;
            let runtime = self.read_quoted_string()?;
            self.expect_char('>')?;
            let ty = crate::HandleTy::new(name, runtime);
            ty.validate()
                .map_err(|error| self.error(error.to_string()))?;
            return Ok(TyG::Handle(Box::new(ty)));
        }

        // Tensor (PKG-U13a): tensor<ELEM, RANK>. The element is an INLINE
        // type, as a vector's is; the grammar takes any element and any u32
        // rank (rank 0 is the scalar tensor), and the integer-element rule is
        // the validator's (`InvalidTensorType`), not the parser's.
        if rem.starts_with("tensor<") {
            self.advance(7)?;
            let elem = self.parse_ty()?;
            self.expect_char(',')?;
            let rank = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(TyG::Tensor(Box::new(elem), rank));
        }

        // Keywords / compound type names
        let ident = self.read_ident()?;
        match ident.as_str() {
            "i8" => Ok(TyG::I8),
            "i16" => Ok(TyG::I16),
            "i32" => Ok(TyG::I32),
            "i64" => Ok(TyG::I64),
            "i128" => Ok(TyG::I128),
            // v25 B1 scalars. Ty::Error has NO parseable spelling (it is
            // producer-internal; its Display form "{error}" is deliberately
            // lexically invalid here) - fail closed.
            "isize" => Ok(TyG::Isize),
            "usize" => Ok(TyG::Usize),
            "char" => Ok(TyG::Char),
            "u8" => Ok(TyG::U8),
            "u16" => Ok(TyG::U16),
            "u32" => Ok(TyG::U32),
            "u64" => Ok(TyG::U64),
            "u128" => Ok(TyG::U128),
            "f16" => Ok(TyG::F16),
            "f32" => Ok(TyG::F32),
            "f64" => Ok(TyG::F64),
            "bool" => Ok(TyG::Bool),
            "ptr" => Ok(TyG::Ptr),
            "!" => Ok(TyG::Never),
            s if s.starts_with("struct.") => {
                let id: u32 = s[7..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid struct id: '{}'", s)))?;
                Ok(TyG::Struct(StructId::new(id)))
            }
            s if s.starts_with("enum.") => {
                let id: u32 = s[5..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid enum id: '{}'", s)))?;
                Ok(TyG::Enum(crate::value::EnumId::new(id)))
            }
            s if s.starts_with("functy.") => {
                let id: u32 = s[7..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid functy id: '{}'", s)))?;
                Ok(TyG::Func(FuncTyId::new(id)))
            }
            s if s.starts_with("record.") => {
                let id: u32 = s[7..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid record id: '{}'", s)))?;
                Ok(TyG::Record(RecordId::new(id)))
            }
            s if s.starts_with("closure.") => {
                let id: u32 = s[8..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid closure id: '{}'", s)))?;
                Ok(TyG::Closure(ClosureTyId::new(id)))
            }
            other => Err(self.error(format!("unknown type: '{}'", other))),
        }
    }

    /// Parse a constant value.
    fn parse_constant<X: ParseExt>(&mut self) -> Result<ConstantG<X>, ParseError> {
        self.skip_whitespace();
        // Amendment S: a template's root `$n` / `?n` (never nested: every child
        // of a constant is level R).
        if let Some(ext) = X::parse_ext(self) {
            return ext.map(ConstantG::Ext);
        }
        let rem = self.remaining();

        // Aggregate: { ... }
        if rem.starts_with('{') {
            self.bump();
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(ConstantG::Aggregate(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("}")?;
            return Ok(ConstantG::Aggregate(elems));
        }

        // Array: array[ ... ]
        if rem.starts_with("array[") {
            self.advance(6)?;
            self.skip_whitespace();
            if self.try_str("]") {
                return Ok(ConstantG::Array(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("]")?;
            return Ok(ConstantG::Array(elems));
        }

        // v50 Splat: `splat[ ELEM; LEN ]` — `LEN` copies of one element (the
        // Rust `[x; N]` spelling). Zero or one copy is spelled `array[ ]` /
        // `array[ x ]`, so a `LEN < 2` is refused exactly as the binary
        // decoder refuses it (one-spelling rule, SPEC_RATIFICATIONS §3.1).
        if rem.starts_with("splat[") {
            self.advance(6)?;
            let elem = self.parse_constant()?;
            self.expect_char(';')?;
            let len = self.read_u64()?;
            self.expect_str("]")?;
            if len < 2 {
                return Err(self.error(format!(
                    "non-canonical splat of {len} element(s): zero or one copy is spelled \
                     array[ .. ] (one-spelling rule, SPEC_RATIFICATIONS §3.1)"
                )));
            }
            return Ok(ConstantG::Splat {
                elem: Box::new(elem),
                len,
            });
        }

        // Vector: vec[ ... ]
        if rem.starts_with("vec[") {
            self.advance(4)?;
            self.skip_whitespace();
            if self.try_str("]") {
                return Ok(ConstantG::Vector(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("]")?;
            return Ok(ConstantG::Vector(elems));
        }

        // Sequence: seq[ ... ]
        if rem.starts_with("seq[") {
            self.advance(4)?;
            self.skip_whitespace();
            if self.try_str("]") {
                return Ok(ConstantG::Sequence(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("]")?;
            return Ok(ConstantG::Sequence(elems));
        }

        // Set: set{ ... }
        if rem.starts_with("set{") {
            self.advance(4)?;
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(ConstantG::Set(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("}")?;
            return Ok(ConstantG::Set(elems));
        }

        // Record: record{ name = val, ... }
        if rem.starts_with("record{") {
            self.advance(7)?;
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(ConstantG::Record(vec![]));
            }
            let mut fields = Vec::new();
            loop {
                self.skip_whitespace();
                let name = self.read_ident()?;
                self.skip_whitespace();
                self.expect_str("=")?;
                let val = self.parse_constant()?;
                fields.push((name, val));
                if !self.try_str(",") {
                    break;
                }
            }
            self.expect_str("}")?;
            return Ok(ConstantG::Record(fields));
        }

        // Closure: closure<func.N>{ c1, c2 }
        if rem.starts_with("closure<func.") {
            self.advance(13)?;
            let func_id = self.read_u32()?;
            self.expect_char('>')?;
            self.skip_whitespace();
            self.expect_char('{')?;
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(ConstantG::Closure {
                    func: FuncId::new(func_id),
                    captures: vec![],
                });
            }
            let mut captures = Vec::new();
            captures.push(self.parse_constant()?);
            while self.try_str(",") {
                captures.push(self.parse_constant()?);
            }
            self.expect_str("}")?;
            return Ok(ConstantG::Closure {
                func: FuncId::new(func_id),
                captures,
            });
        }

        // Bare function item: fndef<func.N>
        if rem.starts_with("fndef<func.") {
            self.advance(11)?;
            let func_id = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(ConstantG::FnDef(FuncId::new(func_id)));
        }

        // v25 Bytes: `bytes<hex>` / `utf8bytes<hex>` — hex payload, two hex
        // digits per byte (the Display form; injective for every byte value).
        // The utf8 claim is CHECKED here, mirroring the binary decoder.
        if rem.starts_with("bytes<") || rem.starts_with("utf8bytes<") {
            let utf8 = rem.starts_with("utf8bytes<");
            self.advance(if utf8 { 10 } else { 6 })?;
            let mut data = Vec::new();
            loop {
                self.skip_whitespace();
                if self.try_str(">") {
                    break;
                }
                let hi = self.expect_hex_digit()?;
                let lo = self.expect_hex_digit()?;
                data.push((hi << 4) | lo);
            }
            if utf8 && std::str::from_utf8(&data).is_err() {
                return Err(self.error("utf8bytes constant carries invalid UTF-8".to_string()));
            }
            return Ok(ConstantG::Bytes { data, utf8 });
        }

        // v70 content-addressed tensor: `tensor_blob<DIGEST>[d0, d1, ..]`, the
        // Display form. The bytes are the module's `blob` rows; whether the
        // digest names one is the validator's question (`MissingBlob`).
        if rem.starts_with("tensor_blob<") {
            self.advance(12)?;
            let digest = self.read_blob_digest()?;
            self.expect_char('>')?;
            self.expect_char('[')?;
            let mut dims = Vec::new();
            self.skip_whitespace();
            if !self.try_str("]") {
                loop {
                    dims.push(self.read_u64()?);
                    self.skip_whitespace();
                    if self.try_str("]") {
                        break;
                    }
                    self.expect_char(',')?;
                }
            }
            return Ok(ConstantG::TensorBlob { digest, dims });
        }

        // Relocatable symbol address: symaddr<name> or symaddr<name + addend>.
        // The `name` is an identifier (function or data-global symbol) and the
        // optional `addend` is a signed integer byte offset. Mirrors the
        // `Display` form so text round-trips.
        if rem.starts_with("symaddr<") {
            self.advance(8)?;
            let symbol = self.read_ident()?;
            self.skip_whitespace();
            let addend = if self.try_str("+") {
                self.skip_whitespace();
                self.read_i64()?
            } else {
                0
            };
            self.skip_whitespace();
            self.expect_char('>')?;
            return Ok(ConstantG::SymbolAddr { symbol, addend });
        }

        // Keyword-boundary peeks read the next CHARACTER (`get(n..)`), never
        // a one-byte window: `get(4..5)` over `trueé` is `None` (byte 5 is
        // inside `é`), which read as "no identifier character follows" and
        // accepted the keyword `true` out of the middle of an identifier.
        if rem.starts_with("phantomdata")
            && !rem
                .get(11..)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            self.advance(11)?;
            return Ok(ConstantG::PhantomData);
        }

        // Crystal lane (E3b, v49): an unwritten aggregate lane. Where it may stand is the
        // validator's rule, not the parser's; the parser reads the spelling wherever a
        // constant is read, exactly as it does `phantomdata`.
        if rem.starts_with("uninit")
            && !rem
                .get(6..7)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            self.advance(6)?;
            return Ok(ConstantG::Uninit);
        }

        // Bool
        if rem.starts_with("true")
            && !rem
                .get(4..)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric())
        {
            self.advance(4)?;
            return Ok(ConstantG::Bool(true));
        }
        if rem.starts_with("false")
            && !rem
                .get(5..)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric())
        {
            self.advance(5)?;
            return Ok(ConstantG::Bool(false));
        }

        // Number: integer or float
        self.parse_number()
    }

    /// Parse a number (int or float). Called after ruling out aggregate/bool.
    ///
    /// Accepts:
    ///   - Integer literals in the full `i128` range (issue #46).
    ///   - Float literals with a decimal point (`42.0`) or exponent
    ///     (`1e300`, `-1.5e-10`), across the full finite `f64` range
    ///     (issue #47).
    ///   - Non-finite float tokens `inf`, `-inf`, `NaN` — the explicit
    ///     spelling emitted by `display::write_constant_float` so that
    ///     `parse(display(Constant::Float(x))) == Constant::Float(x)`
    ///     holds for every `f64` (issue #45).
    fn parse_number<X: ParseExt>(&mut self) -> Result<ConstantG<X>, ParseError> {
        self.skip_whitespace();

        // Non-finite float tokens. Checked before the digit-based
        // lexer so `inf` / `-inf` / `NaN` are never accidentally
        // treated as malformed integer literals.
        if self.try_str("NaN") {
            return Ok(ConstantG::Float(f64::NAN));
        }
        if self.try_str("inf") {
            return Ok(ConstantG::Float(f64::INFINITY));
        }
        if self.remaining().starts_with("-inf") {
            self.advance(4)?;
            return Ok(ConstantG::Float(f64::NEG_INFINITY));
        }

        let start = self.pos;
        let mut is_float = false;

        // Optional leading minus
        if self.peek_char() == Some('-') {
            self.bump();
        }

        // Integer part
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }

        // Decimal part?
        if self.peek_char() == Some('.') {
            is_float = true;
            self.bump();
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.bump();
                } else {
                    break;
                }
            }
        }

        // Exponent?
        if let Some('e' | 'E') = self.peek_char() {
            is_float = true;
            self.bump();
            if self.peek_char() == Some('-') || self.peek_char() == Some('+') {
                self.bump();
            }
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.bump();
                } else {
                    break;
                }
            }
        }

        if self.pos == start {
            return Err(self.error("expected number"));
        }

        let s = &self.input[start..self.pos];
        if is_float {
            // `f64::from_str` accepts the full finite range, including
            // `1e300` / `-1.5e-10`. Non-finite spellings are handled at
            // the top of this function; if one slips through here it was
            // malformed (e.g. `1.e`) and we surface that as an error.
            let v: f64 = s
                .parse()
                .map_err(|_| self.error(format!("invalid float: '{}'", s)))?;
            Ok(ConstantG::Float(v))
        } else {
            // `i128::from_str` accepts the full `i128` range, which is
            // what `Constant::Int` carries. Range-checking against the
            // *declared* integer type (I8/I16/.../I128) is the validator's
            // job, not the lexer's.
            //
            // v24: a NON-NEGATIVE literal above i128::MAX falls through to
            // the u128 path and parses as the canonical `Constant::U128`
            // (one-spelling rule: the variant is picked by VALUE, so
            // `parse(display(x)) == x` holds for the whole 128-bit range).
            if let Ok(v) = s.parse::<i128>() {
                return Ok(ConstantG::Int(v));
            }
            if !s.starts_with('-')
                && let Ok(v) = s.parse::<u128>()
            {
                debug_assert!(v > i128::MAX as u128);
                return Ok(ConstantG::U128(v));
            }
            Err(self.error(format!("invalid integer: '{}'", s)))
        }
    }

    /// Parse a BinOp from its display name.
    fn parse_binop(name: &str) -> Option<BinOp> {
        match name {
            "add" => Some(BinOp::Add),
            "sub" => Some(BinOp::Sub),
            "mul" => Some(BinOp::Mul),
            "udiv" => Some(BinOp::UDiv),
            "sdiv" => Some(BinOp::SDiv),
            "urem" => Some(BinOp::URem),
            "srem" => Some(BinOp::SRem),
            "fadd" => Some(BinOp::FAdd),
            "fsub" => Some(BinOp::FSub),
            "fmul" => Some(BinOp::FMul),
            "fdiv" => Some(BinOp::FDiv),
            "frem" => Some(BinOp::FRem),
            "fmin" => Some(BinOp::FMin),
            "fmax" => Some(BinOp::FMax),
            "and" => Some(BinOp::And),
            "or" => Some(BinOp::Or),
            "xor" => Some(BinOp::Xor),
            // The Bool connectives (4b069189). The printer has spelled them
            // `band`/`bor`/`bxor` since they landed, but the parser did not
            // read them back, so `bxor %b, true` — the ONE spelling of scalar
            // boolean negation (SPEC_RATIFICATIONS §3.2, WS2.21) — could not
            // round-trip through text.
            "band" => Some(BinOp::BAnd),
            "bor" => Some(BinOp::BOr),
            "bxor" => Some(BinOp::BXor),
            "shl" => Some(BinOp::Shl),
            "lshr" => Some(BinOp::LShr),
            "ashr" => Some(BinOp::AShr),
            // WS3.20 (F-057).
            "rotl" => Some(BinOp::RotL),
            "rotr" => Some(BinOp::RotR),
            "fcopysign" => Some(BinOp::FCopySign),
            _ => None,
        }
    }

    fn parse_unop(name: &str) -> Option<UnOp> {
        match name {
            "neg" => Some(UnOp::Neg),
            "fneg" => Some(UnOp::FNeg),
            "fabs" => Some(UnOp::FAbs),
            "fsqrt" => Some(UnOp::FSqrt),
            "ffloor" => Some(UnOp::FFloor),
            "fceil" => Some(UnOp::FCeil),
            "ftrunc" => Some(UnOp::FTrunc),
            "not" => Some(UnOp::Not),
            "ctpop" => Some(UnOp::CtPop),
            // WS3.20 (F-057).
            "ctlz" => Some(UnOp::CtLz),
            "cttz" => Some(UnOp::CtTz),
            "bswap" => Some(UnOp::BSwap),
            "bitreverse" => Some(UnOp::BitReverse),
            _ => None,
        }
    }

    fn parse_castop(name: &str) -> Option<CastOp> {
        match name {
            "trunc" => Some(CastOp::Trunc),
            "zext" => Some(CastOp::ZExt),
            "sext" => Some(CastOp::SExt),
            "fptrunc" => Some(CastOp::FPTrunc),
            "fpext" => Some(CastOp::FPExt),
            "fptoui" => Some(CastOp::FPToUI),
            "fptosi" => Some(CastOp::FPToSI),
            "uitofp" => Some(CastOp::UIToFP),
            "sitofp" => Some(CastOp::SIToFP),
            "ptrtoint" => Some(CastOp::PtrToInt),
            "inttoptr" => Some(CastOp::IntToPtr),
            "ptrtoptr" => Some(CastOp::PtrToPtr),
            "bitcast" => Some(CastOp::Bitcast),
            "transmute" => Some(CastOp::Transmute),
            "reify_fn_pointer" => Some(CastOp::ReifyFnPointer),
            "fptosi.sat" => Some(CastOp::FPToSISat),
            "fptoui.sat" => Some(CastOp::FPToUISat),
            _ => None,
        }
    }

    fn parse_overflow_op(name: &str) -> Option<OverflowOp> {
        match name {
            "add.overflow" => Some(OverflowOp::AddOverflow),
            "sub.overflow" => Some(OverflowOp::SubOverflow),
            "mul.overflow" => Some(OverflowOp::MulOverflow),
            _ => None,
        }
    }

    fn parse_icmpop(name: &str) -> Option<ICmpOp> {
        match name {
            "eq" => Some(ICmpOp::Eq),
            "ne" => Some(ICmpOp::Ne),
            "ult" => Some(ICmpOp::Ult),
            "ule" => Some(ICmpOp::Ule),
            "ugt" => Some(ICmpOp::Ugt),
            "uge" => Some(ICmpOp::Uge),
            "slt" => Some(ICmpOp::Slt),
            "sle" => Some(ICmpOp::Sle),
            "sgt" => Some(ICmpOp::Sgt),
            "sge" => Some(ICmpOp::Sge),
            _ => None,
        }
    }

    fn parse_fcmpop(name: &str) -> Option<FCmpOp> {
        match name {
            "oeq" => Some(FCmpOp::OEq),
            "one" => Some(FCmpOp::ONe),
            "olt" => Some(FCmpOp::OLt),
            "ole" => Some(FCmpOp::OLe),
            "ogt" => Some(FCmpOp::OGt),
            "oge" => Some(FCmpOp::OGe),
            "ueq" => Some(FCmpOp::UEq),
            "une" => Some(FCmpOp::UNe),
            "ult" => Some(FCmpOp::ULt),
            "ule" => Some(FCmpOp::ULe),
            "ugt" => Some(FCmpOp::UGt),
            "uge" => Some(FCmpOp::UGe),
            _ => None,
        }
    }

    fn parse_ordering(&mut self) -> Result<Ordering, ParseError> {
        let name = self.read_ident()?;
        match name.as_str() {
            "relaxed" => Ok(Ordering::Relaxed),
            "acquire" => Ok(Ordering::Acquire),
            "release" => Ok(Ordering::Release),
            "acq_rel" => Ok(Ordering::AcqRel),
            "seq_cst" => Ok(Ordering::SeqCst),
            _ => Err(self.error(format!("unknown ordering: '{}'", name))),
        }
    }

    fn parse_atomicrmwop(name: &str) -> Option<AtomicRMWOp> {
        match name {
            "xchg" => Some(AtomicRMWOp::Xchg),
            "add" => Some(AtomicRMWOp::Add),
            "sub" => Some(AtomicRMWOp::Sub),
            "and" => Some(AtomicRMWOp::And),
            "or" => Some(AtomicRMWOp::Or),
            "xor" => Some(AtomicRMWOp::Xor),
            "max" => Some(AtomicRMWOp::Max),
            "min" => Some(AtomicRMWOp::Min),
            "umax" => Some(AtomicRMWOp::UMax),
            "umin" => Some(AtomicRMWOp::UMin),
            _ => None,
        }
    }

    /// Read an f64 value (possibly negative, possibly integer-looking).
    fn read_f64(&mut self) -> Result<f64, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        // Optional leading minus
        if self.peek_char() == Some('-') {
            self.bump();
        }
        // Integer part
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        // Decimal part
        if self.peek_char() == Some('.') {
            self.bump();
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        // Exponent
        if let Some('e' | 'E') = self.peek_char() {
            self.bump();
            if self.peek_char() == Some('-') || self.peek_char() == Some('+') {
                self.bump();
            }
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        if self.pos == start {
            return Err(self.error("expected f64"));
        }
        let s = &self.input[start..self.pos];
        s.parse::<f64>()
            .map_err(|_| self.error(format!("invalid f64: '{}'", s)))
    }

    fn parse_proof_annotation(&mut self) -> Result<ProofAnnotation, ParseError> {
        let name = self.read_ident()?;
        match name.as_str() {
            "in_bounds" => Ok(ProofAnnotation::InBounds),
            "not_null" => Ok(ProofAnnotation::NotNull),
            "valid_borrow" => Ok(ProofAnnotation::ValidBorrow),
            "unique_borrow" => Ok(ProofAnnotation::UniqueBorrow),
            "shared_borrow" => Ok(ProofAnnotation::SharedBorrow),
            "valid_dealloc" => Ok(ProofAnnotation::ValidDealloc),
            "no_overflow" => Ok(ProofAnnotation::NoOverflow),
            "no_wrap" => Ok(ProofAnnotation::NoWrap),
            "wrapping" => Ok(ProofAnnotation::Wrapping),
            "div_nonzero" => Ok(ProofAnnotation::DivNonZero),
            "shift_in_range" => Ok(ProofAnnotation::ShiftInRange),
            "pure" => Ok(ProofAnnotation::Pure),
            "terminates" => Ok(ProofAnnotation::Terminates),
            "deterministic" => Ok(ProofAnnotation::Deterministic),
            "associative" => Ok(ProofAnnotation::Associative),
            "commutative" => Ok(ProofAnnotation::Commutative),
            "data_race_free" => Ok(ProofAnnotation::DataRaceFree),
            "monotonic" => Ok(ProofAnnotation::Monotonic),
            "no_alias" => Ok(ProofAnnotation::NoAlias),
            "no_panic" => Ok(ProofAnnotation::NoPanic),
            "no_undef" => Ok(ProofAnnotation::NoUndef),
            // Information-flow and havoc markers. These four are nullary and
            // `Display` has always emitted them; the parser arms were missing,
            // so `parse(print(m))` HARD-FAILED on any module carrying one --
            // and two of them (`fresh_symbolic_havoc`, `region_havoc_store`)
            // are emitted in production by trust-ir-bridge, whose canonical
            // text is written out as a shipped `<crate>.trust-ir.txt` artifact.
            "tainted" => Ok(ProofAnnotation::Tainted),
            "trusted_sink" => Ok(ProofAnnotation::TrustedSink),
            "fresh_symbolic_havoc" => Ok(ProofAnnotation::FreshSymbolicHavoc),
            "region_havoc_store" => Ok(ProofAnnotation::RegionHavocStore),
            "readonly_table" => Ok(ProofAnnotation::ReadonlyTable),
            "append_only_buffer" => Ok(ProofAnnotation::AppendOnlyBuffer),
            "atomic_set_insert" => Ok(ProofAnnotation::AtomicSetInsert),
            "parallel_map" => Ok(ProofAnnotation::ParallelMap),
            "bounded_loop" => {
                self.expect_char('(')?;
                let n = self.read_u64()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::BoundedLoop(n))
            }
            "divergence_class" => {
                self.expect_char('(')?;
                let d = self.read_ident()?;
                let div = match d.as_str() {
                    "uniform" => Divergence::Uniform,
                    "low" => Divergence::Low,
                    "high" => Divergence::High,
                    other => {
                        return Err(self.error(format!(
                            "unknown divergence class: '{}' (expected uniform|low|high)",
                            other
                        )));
                    }
                };
                self.expect_char(')')?;
                Ok(ProofAnnotation::DivergenceClass(div))
            }
            "atomic_ordering" => {
                self.expect_char('(')?;
                let ord = self.parse_ordering()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::AtomicOrdering(ord))
            }
            "bounded_output" => {
                self.expect_char('(')?;
                let lo = self.read_f64()?;
                self.expect_char(',')?;
                let hi = self.read_f64()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::BoundedOutput { lo, hi })
            }
            "aligned" => {
                self.expect_char('(')?;
                let n = self.read_u64()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::Aligned(n))
            }
            "proof_ref" => {
                self.expect_char('(')?;
                let n = self.read_u32()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::ProofRef(crate::value::ProofId::new(n)))
            }
            // fast-3 value facts (finding D): `value_range(lo,hi)` carries i128
            // bounds; `known_bits(zeros,ones)` carries u128 masks.
            "value_range" => {
                self.expect_char('(')?;
                let lo = self.read_i128()?;
                self.expect_char(',')?;
                let hi = self.read_i128()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::ValueRange { lo, hi })
            }
            "known_bits" => {
                self.expect_char('(')?;
                let zeros = self.read_u128()?;
                self.expect_char(',')?;
                let ones = self.read_u128()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::KnownBits { zeros, ones })
            }
            "custom" => {
                self.expect_char('(')?;
                let tag = self.read_u32()?;
                self.expect_char(')')?;
                Ok(ProofAnnotation::Custom(ProofTag::new(tag)))
            }
            "branch_weights" => {
                self.expect_char('(')?;
                let mut weights = Vec::new();
                self.skip_whitespace();
                if !self.remaining().starts_with(')') {
                    weights.push(self.read_u32()?);
                    while self.try_str(",") {
                        weights.push(self.read_u32()?);
                    }
                }
                self.expect_char(')')?;
                Ok(ProofAnnotation::BranchWeights(weights))
            }
            other => Err(self.error(format!("unknown proof annotation: '{}'", other))),
        }
    }

    /// Parse the trailing `;`-comment clauses on an instruction node: an
    /// optional `; #proof: ann1, ann2` proof list, an optional
    /// `; #proof_ctx: assumes[..] establishes[..]` per-call-site context
    /// (finding C), an optional `; #loc: <file> <line> <col>` source span,
    /// and an optional v33 `; #scope: <index>` lexical-scope reference. The
    /// clauses may appear in any order on the same line.
    /// A plain `;` comment is skipped to end-of-line; an unknown or
    /// misplaced `; #<word>` directive is REFUSED (roadmap WS4.2).
    fn parse_node_comments(&mut self) -> Result<NodeComments, ParseError> {
        let mut proofs = Vec::new();
        let mut proof_context = None;
        let mut span = None;
        let mut scope = None;
        loop {
            // Peek for a comment without consuming a real newline/next line.
            self.skip_whitespace_no_newline();
            if !self.remaining().starts_with(';') {
                break;
            }
            self.bump(); // the `;`
            let Some(word) = self.read_directive_word()? else {
                // A plain comment: skip the rest of the line and stop.
                self.skip_line()?;
                break;
            };
            self.expect_char(':')?;
            match word {
                directive::PROOF => {
                    proofs.push(self.parse_proof_annotation()?);
                    while self.try_str(",") {
                        proofs.push(self.parse_proof_annotation()?);
                    }
                }
                directive::PROOF_CTX => {
                    proof_context = Some(self.parse_proof_context_clause()?);
                }
                directive::LOC => span = Some(self.parse_loc_clause()?),
                directive::SCOPE => scope = Some(self.read_u32()?),
                other => {
                    return Err(self.error(format!(
                        "directive `{other}` is not valid on an instruction — refusing \
                         rather than dropping it"
                    )));
                }
            }
        }
        Ok((proofs, proof_context, span, scope))
    }

    /// Parse `<file> <line> <col>` (the `; #loc:` body): a zero-based module
    /// file-table index followed by 1-based line and column `u32`s into a
    /// `SourceSpan`. Stays on the current line (no newline consumed).
    fn parse_loc_clause(&mut self) -> Result<SourceSpan, ParseError> {
        self.skip_whitespace_no_newline();
        let file = self.read_u32()?;
        self.skip_whitespace_no_newline();
        let line = self.read_u32()?;
        self.skip_whitespace_no_newline();
        let col = self.read_u32()?;
        Ok(SourceSpan { file, line, col })
    }

    /// Parse `assumes[id,..] establishes[id,..]` (the `; #proof_ctx:` body).
    fn parse_proof_context_clause(&mut self) -> Result<ProofContext, ParseError> {
        self.expect_str("assumes")?;
        let assumes = self.parse_proof_id_bracket_list()?;
        self.expect_str("establishes")?;
        let establishes = self.parse_proof_id_bracket_list()?;
        Ok(ProofContext {
            assumes,
            establishes,
        })
    }

    /// Parse `[id, id, ...]` of `ProofId`s (possibly empty `[]`).
    fn parse_proof_id_bracket_list(&mut self) -> Result<Vec<ProofId>, ParseError> {
        self.expect_char('[')?;
        let mut ids = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with(']') {
            ids.push(ProofId::new(self.read_u32()?));
            while self.try_str(",") {
                ids.push(ProofId::new(self.read_u32()?));
            }
        }
        self.expect_char(']')?;
        Ok(ids)
    }

    /// Parse an instruction (the part after optional results assignment).
    fn parse_instruction<X: ParseExt>(&mut self) -> Result<InstG<X>, ParseError> {
        self.skip_whitespace();
        let rem = self.remaining();

        // Instructions that start with a keyword, in order of specificity.

        // "null ptr"
        if rem.starts_with("null ") {
            self.advance(5)?;
            self.expect_str("ptr")?;
            return Ok(InstG::NullPtr);
        }

        // "global_addr @global.N"
        if rem.starts_with("global_addr ") {
            self.advance(12)?;
            self.expect_str("@global.")?;
            let id = self.read_u32()?;
            return Ok(InstG::GlobalAddr {
                global: GlobalId::new(id),
            });
        }

        // "unreachable"
        if rem.starts_with("unreachable") {
            self.advance(11)?;
            return Ok(InstG::Unreachable);
        }

        // "ret ..."
        if rem.starts_with("ret")
            && rem[3..]
                .chars()
                .next()
                .is_none_or(|c| !c.is_alphanumeric() && c != '_' && c != '.')
        {
            self.advance(3)?;
            let mut values = Vec::new();
            self.skip_whitespace_no_newline();
            // Check if there are values following
            if self.peek_char() == Some('%') {
                values.push(self.read_value_id()?);
                while self.try_str(",") {
                    values.push(self.read_value_id()?);
                }
            }
            return Ok(InstG::Return { values });
        }

        // "br bb..."
        if rem.starts_with("br ") && !rem.starts_with("borrow") {
            self.advance(3)?;
            let target = self.read_block_id()?;
            let args = self.read_block_args()?;
            return Ok(InstG::Br { target, args });
        }

        // "condbr ..."
        if rem.starts_with("condbr ") {
            self.advance(7)?;
            let cond = self.read_value_id()?;
            self.expect_char(',')?;
            let then_target = self.read_block_id()?;
            let then_args = self.read_block_args()?;
            self.expect_char(',')?;
            let else_target = self.read_block_id()?;
            let else_args = self.read_block_args()?;
            return Ok(InstG::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            });
        }

        // "switch ..."
        if rem.starts_with("switch ") {
            self.advance(7)?;
            let value = self.read_value_id()?;
            self.expect_char('[')?;
            let mut cases = Vec::new();
            loop {
                self.skip_whitespace();
                if self.remaining().starts_with("default:") {
                    break;
                }
                // case_value: bbN(args)
                let case_value = self.parse_constant()?;
                self.expect_char(':')?;
                let case_target = self.read_block_id()?;
                let case_args = self.read_block_args()?;
                cases.push(SwitchCase {
                    value: case_value,
                    target: case_target,
                    args: case_args,
                });
            }
            self.expect_str("default:")?;
            let default = self.read_block_id()?;
            let default_args = self.read_block_args()?;
            self.expect_char(']')?;
            // WS4.5: the producer's exhaustiveness hint, a trailing
            // ` exhaustive` bound to this instruction's LINE. Absent means
            // `false` — the sound default that keeps the otherwise arm
            // reachable. The flag is a zero-authority hint either way:
            // `validate_module` re-checks the dead default and the case
            // coverage (WS2.6), exactly as for binary input.
            let before_separator = self.pos;
            self.skip_whitespace_no_newline();
            let exhaustive_enum_unreachable = self.remaining().starts_with("exhaustive")
                && self.input[self.pos + "exhaustive".len()..]
                    .chars()
                    .next()
                    .is_none_or(|ch| ch.is_ascii_whitespace() || ch == ';');
            if exhaustive_enum_unreachable {
                // WS4.5 review: ONE spelling — the printer writes `] exhaustive`
                // with a separating space, so the glued `]exhaustive` is
                // refused rather than accepted as a second spelling.
                if self.pos == before_separator {
                    return Err(self
                        .error("expected whitespace between `]` and `exhaustive` on a `switch`"));
                }
                self.advance("exhaustive".len())?;
            }
            return Ok(InstG::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            });
        }

        // "make_closure closure.N @func.M (%capture, ...)"
        if rem.starts_with("make_closure ") {
            self.advance("make_closure ".len())?;
            let TyG::Closure(ty) = self.parse_ty::<X>()? else {
                return Err(self.error("make_closure requires a closure type"));
            };
            self.expect_str("@func.")?;
            let func = FuncId::new(self.read_u32()?);
            self.expect_char('(')?;
            let mut captures = Vec::new();
            if !self.try_str(")") {
                captures.push(self.read_value_id()?);
                while self.try_str(",") {
                    captures.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            return Ok(InstG::MakeClosure { ty, func, captures });
        }

        // "call @func.N(...)"
        if rem.starts_with("call @func.") || rem.starts_with("call_cannot_unwind @func.") {
            let cannot_unwind = rem.starts_with("call_cannot_unwind @func.");
            self.advance(if cannot_unwind {
                "call_cannot_unwind @func.".len()
            } else {
                11
            })?;
            let func_id = self.read_u32()?;
            self.expect_char('(')?;
            let mut args = Vec::new();
            if !self.try_str(")") {
                args.push(self.read_value_id()?);
                while self.try_str(",") {
                    args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            return Ok(if cannot_unwind {
                InstG::CallCannotUnwind {
                    callee: FuncId::new(func_id),
                    args,
                }
            } else {
                InstG::Call {
                    callee: FuncId::new(func_id),
                    args,
                }
            });
        }

        // "call_indirect %N(functy.M)(args...)"
        if rem.starts_with("call_indirect ") || rem.starts_with("call_indirect_cannot_unwind ") {
            let cannot_unwind = rem.starts_with("call_indirect_cannot_unwind ");
            self.advance(if cannot_unwind {
                "call_indirect_cannot_unwind ".len()
            } else {
                14
            })?;
            let callee = self.read_value_id()?;
            self.expect_char('(')?;
            self.expect_str("functy.")?;
            let sig_id = self.read_u32()?;
            self.expect_char(')')?;
            self.expect_char('(')?;
            let mut args = Vec::new();
            if !self.try_str(")") {
                args.push(self.read_value_id()?);
                while self.try_str(",") {
                    args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            let calling_conv = self.parse_indirect_calling_conv()?;
            return Ok(if cannot_unwind {
                InstG::CallIndirectCannotUnwind {
                    callee,
                    sig: FuncTyId::new(sig_id),
                    args,
                    calling_conv,
                }
            } else {
                InstG::CallIndirect {
                    callee,
                    sig: FuncTyId::new(sig_id),
                    args,
                    calling_conv,
                }
            });
        }

        // "icmp OP TY %a, %b"
        if rem.starts_with("icmp ") {
            self.advance(5)?;
            let op_name = self.read_ident()?;
            let op = Self::parse_icmpop(&op_name)
                .ok_or_else(|| self.error(format!("unknown icmp op: '{}'", op_name)))?;
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(InstG::ICmp { op, ty, lhs, rhs });
        }

        // "fcmp OP TY %a, %b"
        if rem.starts_with("fcmp ") {
            self.advance(5)?;
            let op_name = self.read_ident()?;
            let op = Self::parse_fcmpop(&op_name)
                .ok_or_else(|| self.error(format!("unknown fcmp op: '{}'", op_name)))?;
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(InstG::FCmp { op, ty, lhs, rhs });
        }

        // "[volatile] load TY, ptr %N[, align N]"
        if rem.starts_with("volatile load ") || rem.starts_with("load ") {
            let volatile = if rem.starts_with("volatile ") {
                self.advance(9)?; // "volatile "
                true
            } else {
                false
            };
            self.advance(5)?; // "load "
            let ty = self.parse_ty()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            let align = self.try_parse_align()?;
            return Ok(InstG::Load {
                ty,
                ptr,
                volatile,
                align,
            });
        }

        // "[volatile] store TY %val, ptr %ptr[, align N]"
        if rem.starts_with("volatile store ") || rem.starts_with("store ") {
            let volatile = if rem.starts_with("volatile ") {
                self.advance(9)?; // "volatile "
                true
            } else {
                false
            };
            self.advance(6)?; // "store "
            let ty = self.parse_ty()?;
            let value = self.read_value_id()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            let align = self.try_parse_align()?;
            return Ok(InstG::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            });
        }

        // "alloca TY[, %count][, align N]"
        if rem.starts_with("alloca ") {
            self.advance(7)?;
            let ty = self.parse_ty()?;
            // Parse optional count (starts with %) or align
            let mut count = None;
            let mut align = None;
            if self.try_str(",") {
                self.skip_whitespace_no_newline();
                if self.remaining().starts_with("align ") {
                    self.advance(6)?;
                    align = Some(self.read_u64()?);
                } else {
                    count = Some(self.read_value_id()?);
                    // After count, check for align
                    align = self.try_parse_align()?;
                }
            }
            return Ok(InstG::Alloca { ty, count, align });
        }

        // "heap_alloc ORIGIN TY[, %count][, align N]"
        if rem.starts_with("heap_alloc ") {
            self.advance(11)?;
            let origin = if self.try_str("rust_heap") {
                AllocOrigin::RustHeap
            } else if self.try_str("swift_heap") {
                AllocOrigin::SwiftHeap
            } else if self.try_str("c_malloc") {
                AllocOrigin::CMalloc
            } else if self.try_str("clean_heap") {
                AllocOrigin::CleanHeap
            } else {
                return Err(self.error(
                    "expected heap-alloc origin (rust_heap|swift_heap|c_malloc|clean_heap)",
                ));
            };
            self.skip_whitespace_no_newline();
            let ty = self.parse_ty()?;
            let mut count = None;
            let mut align = None;
            if self.try_str(",") {
                self.skip_whitespace_no_newline();
                if self.remaining().starts_with("align ") {
                    self.advance(6)?;
                    align = Some(self.read_u64()?);
                } else {
                    count = Some(self.read_value_id()?);
                    align = self.try_parse_align()?;
                }
            }
            return Ok(InstG::HeapAlloc {
                ty,
                count,
                align,
                origin,
            });
        }

        // "gep [inbounds] TY, ptr %base, %idx..."
        if rem.starts_with("gep ") {
            self.advance(4)?;
            let inbounds = self.try_str("inbounds ");
            let pointee_ty = self.parse_ty()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let base = self.read_value_id()?;
            let mut indices = Vec::new();
            while self.try_str(",") {
                indices.push(self.read_value_id()?);
            }
            return Ok(InstG::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            });
        }

        // "atomic_load ORDERING TY, ptr %N"
        if rem.starts_with("atomic_load ") {
            self.advance(12)?;
            let ordering = self.parse_ordering()?;
            let ty = self.parse_ty()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::AtomicLoad { ty, ptr, ordering });
        }

        // "atomic_store ORDERING TY %val, ptr %ptr"
        if rem.starts_with("atomic_store ") {
            self.advance(13)?;
            let ordering = self.parse_ordering()?;
            let ty = self.parse_ty()?;
            let value = self.read_value_id()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            });
        }

        // "atomicrmw OP ORDERING TY ptr %ptr, %val"
        if rem.starts_with("atomicrmw ") {
            self.advance(10)?;
            let op_name = self.read_ident()?;
            let op = Self::parse_atomicrmwop(&op_name)
                .ok_or_else(|| self.error(format!("unknown atomicrmw op: '{}'", op_name)))?;
            let ordering = self.parse_ordering()?;
            let ty = self.parse_ty()?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(InstG::AtomicRMW {
                op,
                ty,
                ptr,
                value,
                ordering,
            });
        }

        // "cmpxchg [weak] TY ptr %ptr, %expected, %desired SUCCESS FAILURE"
        if rem.starts_with("cmpxchg ") {
            self.advance(8)?;
            // Crystal lane (D3): the optional LLVM `weak` keyword. No type is spelled `weak`,
            // so reading it here cannot swallow a type name.
            let weak = self.remaining().starts_with("weak ");
            if weak {
                self.advance(5)?;
            }
            let ty = self.parse_ty()?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            self.expect_char(',')?;
            let expected = self.read_value_id()?;
            self.expect_char(',')?;
            let desired = self.read_value_id()?;
            let success = self.parse_ordering()?;
            let failure = self.parse_ordering()?;
            return Ok(InstG::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                success,
                failure,
                weak,
            });
        }

        // "fence ORDERING"
        if rem.starts_with("fence ") {
            self.advance(6)?;
            let ordering = self.parse_ordering()?;
            return Ok(InstG::Fence { ordering });
        }

        // "const TY VALUE"
        if rem.starts_with("const ") {
            self.advance(6)?;
            let ty = self.parse_ty()?;
            let value = self.parse_constant()?;
            return Ok(InstG::Const { ty, value });
        }

        // "undef TY"
        if rem.starts_with("undef ") {
            self.advance(6)?;
            let ty = self.parse_ty()?;
            return Ok(InstG::Undef { ty });
        }

        // "copy TY %N"
        if rem.starts_with("copy ") {
            self.advance(5)?;
            let ty = self.parse_ty()?;
            let operand = self.read_value_id()?;
            return Ok(InstG::Copy { ty, operand });
        }

        // "seq_map_add_k TY %seq, K"  (loopFwd: for x in &mut l { *x += k })
        if rem.starts_with("seq_map_add_k ") {
            self.advance(14)?;
            let ty = self.parse_ty()?;
            let seq = self.read_value_id()?;
            self.expect_char(',')?;
            self.skip_whitespace_no_newline();
            let k = self.read_u64()?;
            return Ok(InstG::SeqMapAddK { ty, seq, k });
        }

        // "seq_map_not TY %seq"  (loopFwd: for b in &mut l { *b = !*b })
        if rem.starts_with("seq_map_not ") {
            self.advance(12)?;
            let ty = self.parse_ty()?;
            let seq = self.read_value_id()?;
            return Ok(InstG::SeqMapNot { ty, seq });
        }

        // "seq_map TY %seq, @func.N"  (general element-op loopFwd:
        // for x in &mut l { *x = fwd(x) }; fwd is a single-&mut element fn).
        // Placed after the longer seq_map_add_k / seq_map_not mnemonics; the
        // trailing space keeps the prefixes disjoint either way.
        if rem.starts_with("seq_map ") {
            self.advance(8)?;
            let ty = self.parse_ty()?;
            let seq = self.read_value_id()?;
            self.expect_char(',')?;
            self.skip_whitespace_no_newline();
            self.expect_str("@func.")?;
            let fwd = self.read_u32()?;
            return Ok(InstG::SeqMap {
                ty,
                seq,
                fwd: FuncId::new(fwd),
            });
        }

        // "select TY %cond, %then, %else"
        if rem.starts_with("select ") {
            self.advance(7)?;
            let ty = self.parse_ty()?;
            let cond = self.read_value_id()?;
            self.expect_char(',')?;
            let then_val = self.read_value_id()?;
            self.expect_char(',')?;
            let else_val = self.read_value_id()?;
            return Ok(InstG::Select {
                ty,
                cond,
                then_val,
                else_val,
            });
        }

        // "assume %N"
        if rem.starts_with("assume ") {
            self.advance(7)?;
            let cond = self.read_value_id()?;
            return Ok(InstG::Assume { cond });
        }

        // "assert %N" (kind `Unspecified`, no site), "assert %N, KIND" (plan
        // item P, wire v52), and either followed by ", panic @func.E at LOC"
        // (amendment P, wire v54: the panic site; LOC is `@global.G` or `%V`).
        // KIND is one of `overflow OP`, `div_by_zero`, `rem_by_zero`,
        // `bounds_check %INDEX, %LEN`, `misaligned_ptr %REQUIRED, %FOUND`,
        // `null_ptr`. Each ", " must follow on the assert's own line.
        if rem.starts_with("assert ") {
            self.advance(7)?;
            let cond = self.read_value_id()?;
            let (kind, site) = self.parse_assert_kind_and_site()?;
            return Ok(InstG::Assert { cond, kind, site });
        }

        // "assert_invoke %N[, KIND], panic @func.E at LOC to bbN(args) unwind
        // bbM" (amendment P, wire v54). The panic clause is required.
        if rem.starts_with("assert_invoke ") {
            self.advance(14)?;
            let cond = self.read_value_id()?;
            let (kind, site) = self.parse_assert_kind_and_site()?;
            let Some(site) = site else {
                return Err(self.error("assert_invoke requires its `panic @func.N at ..` clause"));
            };
            self.skip_whitespace_no_newline();
            self.expect_str("to bb")?;
            let normal = self.read_u32()?;
            self.expect_char('(')?;
            let mut normal_args = Vec::new();
            if !self.try_str(")") {
                normal_args.push(self.read_value_id()?);
                while self.try_str(",") {
                    normal_args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            self.skip_whitespace_no_newline();
            self.expect_str("unwind bb")?;
            let unwind = self.read_u32()?;
            return Ok(InstG::AssertInvoke {
                cond,
                kind,
                site,
                normal_dest: BlockId::new(normal),
                normal_args,
                unwind_dest: BlockId::new(unwind),
            });
        }

        // "borrow_mut %N"
        if rem.starts_with("borrow_mut ") {
            self.advance(11)?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::BorrowMut { ptr });
        }

        // "borrow %N" (check after borrow_mut)
        if rem.starts_with("borrow ") {
            self.advance(7)?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::Borrow { ptr });
        }

        // "end_borrow %N"
        if rem.starts_with("end_borrow ") {
            self.advance(11)?;
            let borrow_ptr = self.read_value_id()?;
            return Ok(InstG::EndBorrow { borrow_ptr });
        }

        // "retain %N"
        if rem.starts_with("retain ") {
            self.advance(7)?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::Retain { ptr });
        }

        // "release %N"
        if rem.starts_with("release ") {
            self.advance(8)?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::Release { ptr });
        }

        // "is_unique %N"
        if rem.starts_with("is_unique ") {
            self.advance(10)?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::IsUnique { ptr });
        }

        // Amendment D: "drop_invoke TY, %ptr to bbN(args) unwind bbM" (wire
        // v55; mirrors `display::write_inst`).
        if rem.starts_with("drop_invoke ") {
            self.advance(12)?;
            let ty = self.parse_ty()?;
            self.expect_char(',')?;
            let ptr = self.read_value_id()?;
            self.skip_whitespace_no_newline();
            self.expect_str("to bb")?;
            let normal = self.read_u32()?;
            self.expect_char('(')?;
            let mut normal_args = Vec::new();
            if !self.try_str(")") {
                normal_args.push(self.read_value_id()?);
                while self.try_str(",") {
                    normal_args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            self.skip_whitespace_no_newline();
            self.expect_str("unwind bb")?;
            let unwind = self.read_u32()?;
            return Ok(InstG::DropInvoke {
                ty,
                ptr,
                normal_dest: BlockId::new(normal),
                normal_args,
                unwind_dest: BlockId::new(unwind),
            });
        }

        // Crystal lane (wave-DS): "drop TY, %ptr" (mirrors `display::write_inst`).
        if rem.starts_with("drop ") {
            self.advance(5)?;
            let ty = self.parse_ty()?;
            self.expect_char(',')?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::Drop { ty, ptr });
        }

        // "dealloc %N"
        if rem.starts_with("dealloc ") {
            self.advance(8)?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::Dealloc { ptr });
        }

        // WS3.20 bulk memory (mirrors `display::write_inst`):
        //   "memcopy [overlap ]ptr %dst, ptr %src, %bytes"
        //   "memset ptr %dst, %byte, %bytes"
        if rem.starts_with("memcopy ") {
            self.advance(8)?;
            let overlap = self.try_str("overlap ");
            self.expect_str("ptr")?;
            let dst = self.read_value_id()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let src = self.read_value_id()?;
            self.expect_char(',')?;
            let bytes = self.read_value_id()?;
            return Ok(InstG::MemCopy {
                dst,
                src,
                bytes,
                overlap,
            });
        }
        if rem.starts_with("memset ") {
            self.advance(7)?;
            self.expect_str("ptr")?;
            let dst = self.read_value_id()?;
            self.expect_char(',')?;
            let byte = self.read_value_id()?;
            self.expect_char(',')?;
            let bytes = self.read_value_id()?;
            return Ok(InstG::MemSet { dst, byte, bytes });
        }

        // Binding-frame instructions. Syntax mirrors `display::write_inst`
        // (crates/trust_ir/src/display.rs:431-455) and is the canonical form
        // emitted by `format::canonical`.

        // `open_frame #<id> "<name>" {slot_name: TY, ...}`
        if rem.starts_with("open_frame ") {
            self.advance(11)?;
            self.skip_whitespace();
            self.expect_char('#')?;
            let id = self.read_u32()?;
            let name = self.read_quoted_string()?;
            self.skip_whitespace();
            self.expect_char('{')?;
            let mut slots = Vec::new();
            // Empty-slot frames render as `{}`.
            if !self.try_str("}") {
                loop {
                    self.skip_whitespace();
                    let slot_name = self.read_ident()?;
                    self.expect_char(':')?;
                    let ty = self.parse_ty()?;
                    slots.push(BindingSlot::new(slot_name, ty));
                    if self.try_str(",") {
                        continue;
                    }
                    self.expect_char('}')?;
                    break;
                }
            }
            return Ok(InstG::OpenFrame {
                def: BindingFrameDef::new(BindingFrameId::new(id), name, slots),
            });
        }

        // `bind_slot %frame, <slot>, %value`
        if rem.starts_with("bind_slot ") {
            self.advance(10)?;
            let frame = self.read_value_id()?;
            self.expect_char(',')?;
            let slot = self.read_u32()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(InstG::BindSlot { frame, slot, value });
        }

        // `load_slot <ty> %frame, <slot>`
        if rem.starts_with("load_slot ") {
            self.advance(10)?;
            let ty = self.parse_ty()?;
            let frame = self.read_value_id()?;
            self.expect_char(',')?;
            let slot = self.read_u32()?;
            return Ok(InstG::LoadSlot { frame, slot, ty });
        }

        // `close_frame %frame`
        if rem.starts_with("close_frame ") {
            self.advance(12)?;
            let frame = self.read_value_id()?;
            return Ok(InstG::CloseFrame { frame });
        }

        // `coro_suspend %frame, <state_slot>, <next_state>, %value`
        if rem.starts_with("coro_suspend ") {
            self.advance(13)?;
            let frame = self.read_value_id()?;
            self.expect_char(',')?;
            let state_slot = self.read_u32()?;
            self.expect_char(',')?;
            let next_state = self.read_i64()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(InstG::CoroSuspend {
                frame,
                state_slot,
                next_state,
                value,
            });
        }

        // "invoke @func.N(args) to bbNORMAL(normal_args) unwind bbUNWIND"
        // Amendment D, Part 2: "invoke_indirect %N(functy.M)(args) [cc=X] to
        // bbN(args) unwind bbM" (wire v56; mirrors `display::write_inst`):
        // `call_indirect`'s spelling, then `invoke`'s successors.
        if rem.starts_with("invoke_indirect ") {
            self.advance("invoke_indirect ".len())?;
            let callee = self.read_value_id()?;
            self.expect_char('(')?;
            self.expect_str("functy.")?;
            let sig_id = self.read_u32()?;
            self.expect_char(')')?;
            self.expect_char('(')?;
            let mut args = Vec::new();
            if !self.try_str(")") {
                args.push(self.read_value_id()?);
                while self.try_str(",") {
                    args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            let calling_conv = self.parse_indirect_calling_conv()?;
            self.skip_whitespace_no_newline();
            self.expect_str("to bb")?;
            let normal = self.read_u32()?;
            self.expect_char('(')?;
            let mut normal_args = Vec::new();
            if !self.try_str(")") {
                normal_args.push(self.read_value_id()?);
                while self.try_str(",") {
                    normal_args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            self.skip_whitespace_no_newline();
            self.expect_str("unwind bb")?;
            let unwind = self.read_u32()?;
            return Ok(InstG::InvokeIndirect {
                callee,
                sig: FuncTyId::new(sig_id),
                args,
                calling_conv,
                normal_dest: BlockId::new(normal),
                normal_args,
                unwind_dest: BlockId::new(unwind),
            });
        }

        if rem.starts_with("invoke @func.") {
            self.advance(13)?;
            let func_id = self.read_u32()?;
            self.expect_char('(')?;
            let mut args = Vec::new();
            if !self.try_str(")") {
                args.push(self.read_value_id()?);
                while self.try_str(",") {
                    args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            self.skip_whitespace_no_newline();
            self.expect_str("to bb")?;
            let normal = self.read_u32()?;
            self.expect_char('(')?;
            let mut normal_args = Vec::new();
            if !self.try_str(")") {
                normal_args.push(self.read_value_id()?);
                while self.try_str(",") {
                    normal_args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            self.skip_whitespace_no_newline();
            self.expect_str("unwind bb")?;
            let unwind = self.read_u32()?;
            return Ok(InstG::Invoke {
                callee: FuncId::new(func_id),
                args,
                normal_dest: BlockId::new(normal),
                normal_args,
                unwind_dest: BlockId::new(unwind),
            });
        }

        // "landingpad [cleanup] [catch i0, i1, ..]"
        if rem.starts_with("landingpad") {
            self.advance(10)?;
            self.skip_whitespace_no_newline();
            let is_cleanup = self.try_str("cleanup");
            self.skip_whitespace_no_newline();
            let mut catch_type_indices = Vec::new();
            if self.try_str("catch") {
                self.skip_whitespace_no_newline();
                catch_type_indices.push(self.read_u32()?);
                while self.try_str(",") {
                    self.skip_whitespace_no_newline();
                    catch_type_indices.push(self.read_u32()?);
                }
            }
            return Ok(InstG::LandingPad {
                is_cleanup,
                catch_type_indices,
            });
        }

        // "resume %exn"
        if rem.starts_with("resume ") {
            self.advance(7)?;
            let exn = self.read_value_id()?;
            return Ok(InstG::Resume { exn });
        }

        // WS3.5: "make_aggregate TY [variant N] (%a, %b)". Matched BEFORE the
        // other aggregate mnemonics purely for locality; the prefixes are
        // disjoint. An empty lane list is `()` (a unit struct / empty tuple /
        // a fieldless enum variant), never an omitted parenthesis.
        if rem.starts_with("make_aggregate ") {
            self.advance(15)?;
            let ty = self.parse_ty()?;
            let variant = if self.try_str("variant") {
                Some(self.read_u32()?)
            } else {
                None
            };
            self.expect_char('(')?;
            let mut fields = Vec::new();
            if !self.try_str(")") {
                fields.push(self.read_value_id()?);
                while self.try_str(",") {
                    fields.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            return Ok(InstG::MakeAggregate {
                ty,
                variant,
                fields,
            });
        }

        // v50: "array_splat [E x N] %v" — N copies of one register value.
        if rem.starts_with("array_splat ") {
            self.advance(12)?;
            let ty = self.parse_ty()?;
            let value = self.read_value_id()?;
            return Ok(InstG::ArraySplat { ty, value });
        }

        // PKG-U13a: "tensor_contract TY %lhs, %rhs batch [a:b, ...] contract
        // [a:b, ...]". Both clauses are mandatory and in that order (an empty
        // list is `[]`), exactly as `display::write_inst` prints them. Axis
        // range, distinctness and the result rank are the validator's
        // (`InvalidTensorContract`), not the grammar's.
        if rem.starts_with("tensor_contract ") {
            self.advance("tensor_contract ".len())?;
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            self.expect_str("batch")?;
            let batch = self.read_axis_pairs()?;
            self.expect_str("contract")?;
            let contract = self.read_axis_pairs()?;
            return Ok(InstG::TensorContract {
                ty,
                lhs,
                rhs,
                batch,
                contract,
            });
        }

        // PKG-U13c: "tensor_map TY (%a, ...) { NODE; ... }". The operand
        // list and the body are always written (`()` and `{ }` when empty);
        // the typing and lane rules are the validator's (`InvalidTensorMap`).
        if rem.starts_with("tensor_map ") {
            self.advance("tensor_map ".len())?;
            let ty = self.parse_ty()?;
            self.expect_char('(')?;
            let mut args = Vec::new();
            if !self.try_str(")") {
                args.push(self.read_value_id()?);
                while self.try_str(",") {
                    args.push(self.read_value_id()?);
                }
                self.expect_char(')')?;
            }
            self.expect_char('{')?;
            let mut body = Vec::new();
            if !self.try_str("}") {
                body.push(self.parse_tensor_map_node()?);
                while self.try_str(";") {
                    body.push(self.parse_tensor_map_node()?);
                }
                self.expect_char('}')?;
            }
            return Ok(InstG::TensorMap { ty, args, body });
        }

        // PKG-U13c: "tensor_reduce OP TY %x axes [a, ...] order row_major".
        // Both clauses are mandatory and in that order.
        if rem.starts_with("tensor_reduce ") {
            self.advance("tensor_reduce ".len())?;
            let op_name = self.read_ident()?;
            let op = crate::TensorReduceOp::ALL
                .into_iter()
                .find(|op| op.name() == op_name)
                .ok_or_else(|| self.error(format!("unknown tensor_reduce op: '{op_name}'")))?;
            let ty = self.parse_ty()?;
            let src = self.read_value_id()?;
            self.expect_str("axes")?;
            let axes = self.read_bracketed(Self::read_u32)?;
            self.expect_str("order")?;
            let order_name = self.read_ident()?;
            let order = match order_name.as_str() {
                "row_major" => crate::TensorReduceOrder::RowMajor,
                _ => return Err(self.error(format!("unknown tensor_reduce order: '{order_name}'"))),
            };
            return Ok(InstG::TensorReduce {
                ty,
                src,
                op,
                axes,
                order,
            });
        }

        // PKG-U13c: "tensor_view TY %src params [%p, ...] exprs [NODE, ...]
        // shape [$i, ...] index [$j, ...]" and an optional "fill %f". Every
        // list clause is mandatory and in that order; the node, phase and
        // typing rules are the validator's (`InvalidTensorView`).
        if rem.starts_with("tensor_view ") {
            self.advance("tensor_view ".len())?;
            let ty = self.parse_ty()?;
            let src = self.read_value_id()?;
            self.expect_str("params")?;
            let params = self.read_bracketed(Self::read_value_id)?;
            self.expect_str("exprs")?;
            let exprs = self.read_bracketed(Self::parse_tensor_index_expr)?;
            self.expect_str("shape")?;
            let shape = self.read_bracketed(Self::read_lane)?;
            self.expect_str("index")?;
            let index = self.read_bracketed(Self::read_lane)?;
            // The optional clause is looked for on this line only: the next
            // line (a comment, a directive, the terminator) is never read as
            // part of the view.
            self.skip_whitespace_no_newline();
            let fill = if self.remaining().starts_with("fill") && self.consume_keyword("fill") {
                Some(self.read_value_id()?)
            } else {
                None
            };
            return Ok(InstG::TensorView {
                ty,
                src,
                params,
                exprs,
                shape,
                index,
                fill,
            });
        }

        // PKG-U13d: "tensor_gather TY %data coords [%c, ...]". The coordinate
        // clause is mandatory (`[]` when empty); the rank and element rules
        // are the validator's (`InvalidTensorGather`).
        if rem.starts_with("tensor_gather ") {
            self.advance("tensor_gather ".len())?;
            let ty = self.parse_ty()?;
            let data = self.read_value_id()?;
            self.expect_str("coords")?;
            let coords = self.read_bracketed(Self::read_value_id)?;
            return Ok(InstG::TensorGather { ty, data, coords });
        }

        // PKG-U13d: "tensor_scatter TY %init, %src coords [%c, ...]"; the
        // rules are the validator's (`InvalidTensorScatter`).
        if rem.starts_with("tensor_scatter ") {
            self.advance("tensor_scatter ".len())?;
            let ty = self.parse_ty()?;
            let init = self.read_value_id()?;
            self.expect_char(',')?;
            let src = self.read_value_id()?;
            self.expect_str("coords")?;
            let coords = self.read_bracketed(Self::read_value_id)?;
            return Ok(InstG::TensorScatter {
                ty,
                init,
                src,
                coords,
            });
        }

        // "extractfield TY %agg, FIELD"
        if rem.starts_with("extractfield ") {
            self.advance(13)?;
            let ty = self.parse_ty()?;
            let aggregate = self.read_value_id()?;
            self.expect_char(',')?;
            let field = self.read_u32()?;
            return Ok(InstG::ExtractField {
                ty,
                aggregate,
                field,
            });
        }

        // "insertfield TY %agg, FIELD, %val"
        if rem.starts_with("insertfield ") {
            self.advance(12)?;
            let ty = self.parse_ty()?;
            let aggregate = self.read_value_id()?;
            self.expect_char(',')?;
            let field = self.read_u32()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(InstG::InsertField {
                ty,
                aggregate,
                field,
                value,
            });
        }

        // "extractelement TY %arr, %idx"
        if rem.starts_with("extractelement ") {
            self.advance(15)?;
            let ty = self.parse_ty()?;
            let array = self.read_value_id()?;
            self.expect_char(',')?;
            let index = self.read_value_id()?;
            return Ok(InstG::ExtractElement { ty, array, index });
        }

        // "insertelement TY %arr, %idx, %val"
        if rem.starts_with("insertelement ") {
            self.advance(14)?;
            let ty = self.parse_ty()?;
            let array = self.read_value_id()?;
            self.expect_char(',')?;
            let index = self.read_value_id()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(InstG::InsertElement {
                ty,
                array,
                index,
                value,
            });
        }

        // "ptr_data PTR_TY %ptr"
        if rem.starts_with("ptr_data ") {
            self.advance(9)?;
            let ptr_ty = self.parse_ty()?;
            let ptr = self.read_value_id()?;
            return Ok(InstG::PtrData { ptr_ty, ptr });
        }

        // "ptr_metadata PTR_TY %ptr to META_TY"
        if rem.starts_with("ptr_metadata ") {
            self.advance(13)?;
            let ptr_ty = self.parse_ty()?;
            let ptr = self.read_value_id()?;
            self.expect_str("to")?;
            let metadata_ty = self.parse_ty()?;
            return Ok(InstG::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            });
        }

        // "ptr_from_parts PTR_TY ptr %data, META_TY %metadata"
        if rem.starts_with("ptr_from_parts ") {
            self.advance(15)?;
            let ptr_ty = self.parse_ty()?;
            self.expect_str("ptr")?;
            let data = self.read_value_id()?;
            self.expect_char(',')?;
            let metadata_ty = self.parse_ty()?;
            let metadata = self.read_value_id()?;
            return Ok(InstG::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            });
        }

        // "dialect_op <dialect>.<op>(%0, %1, ...) [-> TY | -> (TY, TY, ...)] [key=val]* [v<version>]"
        if rem.starts_with("dialect_op ") {
            self.advance(11)?;
            return self.parse_dialect_op();
        }

        // Now try generic patterns: OPNAME TY %lhs, %rhs (BinOp, OverflowOp, UnOp, CastOp)
        let opname = self.read_ident()?;

        // OverflowOp: "add.overflow TY %a, %b"
        if let Some(op) = Self::parse_overflow_op(&opname) {
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(InstG::Overflow { op, ty, lhs, rhs });
        }

        // BinOp: "add TY %a, %b"
        if let Some(op) = Self::parse_binop(&opname) {
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(InstG::BinOp { op, ty, lhs, rhs });
        }

        // UnOp: "neg TY %a"
        if let Some(op) = Self::parse_unop(&opname) {
            let ty = self.parse_ty()?;
            let operand = self.read_value_id()?;
            return Ok(InstG::UnOp { op, ty, operand });
        }

        // CastOp: "sext TY %a to TY"
        if let Some(op) = Self::parse_castop(&opname) {
            let src_ty = self.parse_ty()?;
            let operand = self.read_value_id()?;
            self.expect_str("to")?;
            let dst_ty = self.parse_ty()?;
            return Ok(InstG::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            });
        }

        Err(self.error(format!("unknown instruction: '{}'", opname)))
    }

    /// Parse the body of a `dialect_op` instruction after the keyword has been
    /// consumed. Mirrors `display::write_dialect_op`.
    fn parse_dialect_op<X: ParseExt>(&mut self) -> Result<InstG<X>, ParseError> {
        use crate::dialect::{AttrEntry, DialectInst};
        self.skip_whitespace();
        // `<dialect>.<op>` — read_ident accepts dots, so we split on the first dot.
        let qualified = self.read_ident()?;
        let (dialect, op) = match qualified.find('.') {
            Some(i) if i > 0 && i + 1 < qualified.len() => {
                (qualified[..i].to_string(), qualified[i + 1..].to_string())
            }
            _ => {
                return Err(self.error(format!(
                    "expected '<dialect>.<op>' in dialect_op, got '{}'",
                    qualified
                )));
            }
        };

        // Operand list: (%0, %1, ...)
        self.expect_char('(')?;
        let mut operands = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with(')') {
            operands.push(self.read_value_id()?);
            while self.try_str(",") {
                operands.push(self.read_value_id()?);
            }
        }
        self.expect_char(')')?;

        // Optional result type(s): ` -> Ty` or ` -> (Ty, Ty, ...)`
        let mut result_tys = Vec::new();
        if self.try_str("->") {
            self.skip_whitespace();
            if self.try_str("(") {
                self.skip_whitespace();
                if !self.remaining().starts_with(')') {
                    result_tys.push(self.parse_ty()?);
                    while self.try_str(",") {
                        result_tys.push(self.parse_ty()?);
                    }
                }
                self.expect_char(')')?;
            } else {
                result_tys.push(self.parse_ty()?);
            }
        }

        // Optional `[name=value]` attributes (zero or more).
        let mut attrs = Vec::new();
        loop {
            if !self.try_str("[") {
                break;
            }
            let name = self.read_ident()?;
            self.expect_char('=')?;
            let value = self.parse_attr_value()?;
            self.expect_char(']')?;
            attrs.push(AttrEntry { name, value });
        }

        // Optional version suffix: `v<N>`. Version 1 is the default and is
        // omitted by the writer.
        let mut version: u32 = 1;
        // Save position — only consume `v` if it is followed by digits.
        let saved = (self.pos, self.line, self.col);
        self.skip_whitespace();
        if self.remaining().starts_with('v') {
            self.bump();
            if self
                .peek_char()
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false)
            {
                version = self.read_u32()?;
            } else {
                // Not a version tag; restore.
                self.pos = saved.0;
                self.line = saved.1;
                self.col = saved.2;
            }
        } else {
            self.pos = saved.0;
            self.line = saved.1;
            self.col = saved.2;
        }

        let mut inst = DialectInst::new(dialect, op);
        inst.operands = operands;
        inst.result_tys = result_tys;
        inst.attrs = attrs;
        inst.version = version;
        Ok(InstG::DialectOp(Box::new(inst)))
    }

    /// Parse an `AttrValue` in the `<tag>:<payload>` form emitted by the display
    /// writer. Mirrors `display::write_attr_value`.
    fn parse_attr_value(&mut self) -> Result<crate::dialect::AttrValue, ParseError> {
        use crate::dialect::AttrValue;
        self.skip_whitespace();
        // Tag is a bare identifier.
        let tag = self.read_ident()?;
        self.expect_char(':')?;
        match tag.as_str() {
            "i64" => {
                // Optional leading '-'.
                self.skip_whitespace();
                let start = self.pos;
                if self.peek_char() == Some('-') {
                    self.bump();
                }
                while let Some(ch) = self.peek_char() {
                    if ch.is_ascii_digit() {
                        self.bump();
                    } else {
                        break;
                    }
                }
                if self.pos == start {
                    return Err(self.error("expected i64"));
                }
                let s = &self.input[start..self.pos];
                let v: i64 = s
                    .parse()
                    .map_err(|_| self.error(format!("invalid i64: '{}'", s)))?;
                Ok(AttrValue::I64(v))
            }
            "u64" => {
                let v = self.read_u64()?;
                Ok(AttrValue::U64(v))
            }
            "f64" => {
                // Two forms (finding F): `bits(<u64>)` for an exact bit
                // pattern (covers NaN/±inf) or a plain decimal for finite
                // values.
                self.skip_whitespace();
                if self.try_str("bits(") {
                    let bits = self.read_u64()?;
                    self.expect_char(')')?;
                    Ok(AttrValue::F64(f64::from_bits(bits)))
                } else {
                    let v = self.read_f64()?;
                    Ok(AttrValue::F64(v))
                }
            }
            "bool" => {
                self.skip_whitespace();
                if self.try_str("true") {
                    Ok(AttrValue::Bool(true))
                } else if self.try_str("false") {
                    Ok(AttrValue::Bool(false))
                } else {
                    Err(self.error("expected 'true' or 'false' for bool attr"))
                }
            }
            "str" => {
                let s = self.read_quoted_string()?;
                Ok(AttrValue::Str(s))
            }
            "bytes" => {
                // Format: `bytes:<len>:<hex>` — the tag's colon has already
                // been consumed, so we read the length then another colon.
                //
                // The digits are consumed ONE ASCII HEX DIGIT at a time
                // through `expect_hex_digit`, never by slicing
                // `input[start..start + 2 * len]`: the declared length is
                // untrusted input, and a byte-count slice over a payload
                // carrying a multi-byte character would panic on a char
                // boundary (the c09 class) — and `len * 2` on an
                // attacker-chosen `u64` could overflow before the slice.
                let declared = self.read_u64()?;
                self.expect_char(':')?;
                let len = usize::try_from(declared)
                    .ok()
                    .and_then(|len| len.checked_mul(2).map(|hex_len| (len, hex_len)))
                    .filter(|&(_, hex_len)| hex_len <= self.remaining().len())
                    .map(|(len, _)| len)
                    .ok_or_else(|| {
                        self.error(format!(
                            "expected {} hex chars for bytes attr, got {}",
                            declared.saturating_mul(2),
                            self.remaining().len()
                        ))
                    })?;
                let mut bytes = Vec::with_capacity(len);
                for _ in 0..len {
                    let hi = self.expect_hex_digit()?;
                    let lo = self.expect_hex_digit()?;
                    bytes.push((hi << 4) | lo);
                }
                Ok(AttrValue::Bytes(bytes))
            }
            "ty" => {
                let t = self.parse_ty()?;
                Ok(AttrValue::Ty(t))
            }
            other => Err(self.error(format!("unknown attr tag '{}'", other))),
        }
    }

    /// Parse a single instruction line (with optional result assignment).
    fn parse_instr_node<X: ParseExt>(&mut self) -> Result<InstrNodeG<X>, ParseError> {
        self.skip_whitespace();

        // Check for result(s): %N = ... or %N, %M = ...
        let mut results = Vec::new();
        let saved = (self.pos, self.line, self.col);
        if self.remaining().starts_with('%') {
            // Try to parse results
            let first = self.read_value_id()?;
            results.push(first);
            while self.try_str(",") {
                if self.remaining().trim_start().starts_with('%') {
                    // Might be another result before '='
                    let saved2 = (self.pos, self.line, self.col);
                    let next = self.read_value_id()?;
                    // Peek ahead for '=' or ','
                    self.skip_whitespace();
                    if self.remaining().starts_with('=') || self.remaining().starts_with(',') {
                        results.push(next);
                    } else {
                        // Backtrack: this wasn't a result
                        self.pos = saved2.0;
                        self.line = saved2.1;
                        self.col = saved2.2;
                        break;
                    }
                } else {
                    break;
                }
            }
            if self.try_str("=") {
                // Results confirmed
            } else {
                // No '=' found, backtrack - this is an instruction starting with %
                self.pos = saved.0;
                self.line = saved.1;
                self.col = saved.2;
                results.clear();
            }
        }

        let inst = self.parse_instruction()?;
        let (proofs, proof_context, span, scope) = self.parse_node_comments()?;

        let mut node = InstrNodeG::new(inst);
        for r in results {
            node = node.with_result(r);
        }
        for p in proofs {
            node = node.with_proof(p);
        }
        if let Some(ctx) = proof_context {
            node = node.with_proof_context(ctx);
        }
        if let Some(s) = span {
            node = node.with_span(s);
        }
        if let Some(scope) = scope {
            node = node.with_scope(scope);
        }
        Ok(node)
    }

    /// Parse a basic block.
    fn parse_block<X: ParseExt>(&mut self) -> Result<BlockG<X>, ParseError> {
        self.skip_whitespace();
        let id = self.read_block_id()?;

        // Optional params: (%N: TY, %M: TY)
        let mut params = Vec::new();
        if self.try_str("(") && !self.try_str(")") {
            loop {
                let val = self.read_value_id()?;
                self.expect_char(':')?;
                let ty = self.parse_ty()?;
                params.push((val, ty));
                if !self.try_str(",") {
                    break;
                }
            }
            self.expect_char(')')?;
        }

        self.expect_char(':')?;

        let mut block = BlockG::new(id);
        block.params = params;

        // Parse instructions until we hit a line that starts a new block or '}'
        loop {
            self.skip_whitespace();
            let rem = self.remaining();
            if rem.is_empty() || rem.starts_with('}') || rem.starts_with("bb") {
                // Check if it's actually a new block (bb followed by digit)
                if let Some(after_bb) = rem.strip_prefix("bb")
                    && after_bb.chars().next().is_some_and(|c| c.is_ascii_digit())
                {
                    break;
                }
                if rem.is_empty() || rem.starts_with('}') {
                    break;
                }
            }
            let node = self.parse_instr_node()?;
            block.body.push(node);
        }

        Ok(block)
    }

    /// Parse a function definition.
    fn parse_function<X: ParseExt>(&mut self) -> Result<(FunctionG<X>, FuncTyId), ParseError> {
        self.skip_whitespace();
        // Parse optional linkage and calling convention before 'fn'
        let linkage = self.try_parse_linkage()?;
        let calling_conv = self.try_parse_calling_conv()?;
        self.expect_str("fn")?;
        self.expect_char('@')?;
        // Read the function name: bare alphabet, or a quoted escaped name.
        let name = self.read_symbol()?;
        self.expect_char('(')?;
        self.expect_str("functy.")?;
        let ft_idx = self.read_u32()?;
        self.expect_char(')')?;
        self.expect_char('{')?;

        let ft_id = FuncTyId::new(ft_idx);
        // We need a FuncId but we'll set it later
        let mut func = FunctionG::new(FuncId::new(0), name, ft_id, BlockId::new(0));
        func.linkage = linkage;
        func.calling_conv = calling_conv;
        // v45 symbol directives whose default is a legal stated value
        // (`default`, `false`), so presence — not the field — records that
        // one was already read.
        let mut seen_visibility = false;
        let mut seen_retained = false;
        // WS4.4: the summary block is ONE contiguous run in a fixed order
        // (`#summary`, `#requires`*, `#ensures`*, `#decreases`*,
        // `#backed-by`?, `#effects`?), so printer output has a single spelling.
        let mut summary_block = SummaryBlock::NotStarted;

        // Function-level proof annotations and attributes (finding B). These
        // are `;`-comment lines emitted between `fn ... {` and the first block.
        // Parse any number of them, in any order, before the blocks.
        loop {
            self.skip_whitespace();
            if !self.at_directive() {
                break;
            }
            self.bump(); // the `;`
            // Roadmap WS4.2: one shared vocabulary; an unknown or misplaced
            // word is refused, never skipped.
            let Some(word) = self.read_directive_word()? else {
                break;
            };
            if word != directive::PARAM_ATTRS {
                self.expect_char(':')?;
            }
            let summary_phase = SummaryBlock::phase_of(word);
            if summary_phase.is_none() && matches!(summary_block, SummaryBlock::Open(_)) {
                // Any other directive closes the block for good.
                summary_block = SummaryBlock::Closed;
            }
            if let Some(phase) = summary_phase {
                summary_block = self.parse_summary_directive(&mut func, summary_block, phase)?;
            } else if word == directive::PROOF {
                func.proofs.push(self.parse_proof_annotation()?);
                while self.try_str(",") {
                    func.proofs.push(self.parse_proof_annotation()?);
                }
            } else if word == directive::ATTRS {
                self.parse_func_attr_flags(&mut func.attrs)?;
            } else if word == directive::PARAM_ATTRS {
                self.parse_param_attrs(&mut func.attrs)?;
            } else if word == directive::RET_ATTRS {
                // v45 (WS3.11): the return slot, same grammar as a parameter.
                // Stated once: a second line is two claims about one slot,
                // refused rather than letting the later one win (review).
                if !func.attrs.ret.is_empty() {
                    return Err(self.error("duplicate #ret_attrs directive"));
                }
                func.attrs.ret = self.parse_slot_attrs()?;
            } else if word == directive::PRODUCER {
                func.producer = Some(self.parse_producer()?);
            } else if word == directive::BODY_GATE {
                if func.body_gate.is_some() {
                    return Err(self.error("duplicate #body-gate directive"));
                }
                func.body_gate = Some(self.parse_body_gate()?);
            } else if word == directive::TARGET_FEATURES {
                loop {
                    self.skip_whitespace_no_newline();
                    if self.peek_char().is_none_or(|c| c == '\n') {
                        break;
                    }
                    func.attrs.target_features.push(self.read_quoted_string()?);
                    self.skip_whitespace_no_newline();
                    if self.peek_char() == Some(',') {
                        self.bump();
                    } else {
                        break;
                    }
                }
            } else if word == directive::DISPLAY_PATH {
                if func.display_path.is_some() {
                    return Err(self.error("duplicate #display-path directive"));
                }
                self.skip_whitespace_no_newline();
                func.display_path = Some(self.read_quoted_string()?);
            } else if word == directive::SECTION {
                // v45 (WS3.10). The quoted form is the inverse of the Debug
                // escaping the printer uses, so any section string round-trips.
                if func.section.is_some() {
                    return Err(self.error("duplicate #section directive"));
                }
                self.skip_whitespace_no_newline();
                func.section = Some(self.read_quoted_string()?);
            } else if word == directive::VISIBILITY {
                // Stated once (review): `hidden` then `default` is a
                // contradiction, not a correction.
                if seen_visibility {
                    return Err(self.error("duplicate #visibility directive"));
                }
                seen_visibility = true;
                self.skip_whitespace_no_newline();
                let token = self.read_ident()?;
                func.visibility = match token.as_str() {
                    "default" => crate::Visibility::Default,
                    "hidden" => crate::Visibility::Hidden,
                    "protected" => crate::Visibility::Protected,
                    other => {
                        return Err(self.error(format!(
                            "unknown visibility '{other}' (expected default, hidden, protected)"
                        )));
                    }
                };
            } else if word == directive::RETAINED {
                // v45 (WS3.10): `; #retained: true` — the value is spelled so
                // the directive keeps the one `<word>:` grammar. Stated once
                // (review), like `#visibility`.
                if seen_retained {
                    return Err(self.error("duplicate #retained directive"));
                }
                seen_retained = true;
                self.skip_whitespace_no_newline();
                let token = self.read_ident()?;
                func.retained = match token.as_str() {
                    "true" => true,
                    "false" => false,
                    other => {
                        return Err(self.error(format!(
                            "expected `true`/`false` for #retained, got '{other}'"
                        )));
                    }
                };
            } else if word == directive::NAMES {
                func.value_names = Some(self.parse_value_names()?);
            } else if word == directive::SCOPE {
                let (index, scope) = self.parse_scope_data()?;
                let scopes = func.scopes.get_or_insert_with(Vec::new);
                if index as usize != scopes.len() {
                    return Err(self.error(format!(
                        "function scope entry {index} out of order (expected {})",
                        scopes.len()
                    )));
                }
                scopes.push(scope);
            } else if word == directive::SOURCE_PROVENANCE {
                if func.source_provenance.is_some() {
                    return Err(self.error("duplicate #source-provenance directive"));
                }
                self.expect_str("schema")?;
                let schema = self.read_u32()?;
                self.expect_str("compiler")?;
                let compiler_source_digest = self.read_source_provenance_digest()?;
                self.expect_str("semantic")?;
                let semantic_body_digest = self.read_source_provenance_digest()?;
                self.expect_str("binding")?;
                let binding_digest = self.read_source_provenance_digest()?;
                func.source_provenance = Some(SourceProvenance {
                    schema,
                    compiler_source_digest,
                    semantic_body_digest,
                    binding_digest,
                    loops: Vec::new(),
                });
            } else if word == directive::SOURCE_LOOP {
                let source_loop_id = self.read_u32()?;
                self.expect_str("hir")?;
                let hir_local_id = self.read_u32()?;
                self.expect_str("header")?;
                let header = BlockId::new(self.read_u32()?);
                let Some(provenance) = func.source_provenance.as_mut() else {
                    return Err(self
                        .error("#source-loop requires a preceding #source-provenance directive"));
                };
                if provenance
                    .loops
                    .iter()
                    .any(|source_loop| source_loop.source_loop_id == source_loop_id)
                {
                    return Err(self.error(format!("duplicate #source-loop id {source_loop_id}")));
                }
                provenance.loops.push(SourceLoopProvenance {
                    source_loop_id,
                    hir_local_id,
                    header,
                    bindings: Vec::new(),
                });
            } else if word == directive::SOURCE_BINDING {
                self.expect_str("loop")?;
                let source_loop_id = self.read_u32()?;
                self.expect_str("name")?;
                let name = self.read_quoted_string()?;
                self.expect_str("hir")?;
                let hir_local_id = self.read_u32()?;
                self.skip_whitespace_no_newline();
                let place = if self.try_str("function-param") {
                    SourcePlace::FunctionParameter {
                        index: self.read_u32()?,
                    }
                } else if self.try_str("loop-param") {
                    SourcePlace::LoopParameter {
                        index: self.read_u32()?,
                    }
                } else {
                    return Err(self.error(
                        "expected #source-binding place kind 'function-param' or 'loop-param'",
                    ));
                };
                let Some(provenance) = func.source_provenance.as_mut() else {
                    return Err(self.error(
                        "#source-binding requires a preceding #source-provenance directive",
                    ));
                };
                let matches = provenance
                    .loops
                    .iter()
                    .enumerate()
                    .filter(|(_, source_loop)| source_loop.source_loop_id == source_loop_id)
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>();
                let [source_loop_index] = matches.as_slice() else {
                    return Err(self.error(format!(
                        "#source-binding loop {source_loop_id} must name exactly one preceding #source-loop"
                    )));
                };
                provenance.loops[*source_loop_index]
                    .bindings
                    .push(SourceBindingProvenance {
                        name,
                        hir_local_id,
                        place,
                    });
            } else {
                // In the vocabulary, but not a function-header directive
                // (`#loc`, `#proof_ctx` belong to instruction nodes).
                return Err(self.error(format!(
                    "directive `{word}` is not valid in a function header — refusing rather \
                     than dropping it"
                )));
            }
        }

        // Parse blocks
        loop {
            self.skip_whitespace();
            if self.try_str("}") {
                break;
            }
            let block = self.parse_block()?;
            func.blocks.push(block);
        }

        // Entry block is the first block
        if let Some(first) = func.blocks.first() {
            func.entry = first.id;
        }

        Ok((func, ft_id))
    }

    /// WS4.4 (F-064): one directive of the function-summary block, after its
    /// `word:`. `state` is the block's state BEFORE this directive; the
    /// returned state replaces it.
    ///
    /// Refused, each by name: a clause line with no preceding `#summary`, a
    /// second `#summary`, a block that is not contiguous, a directive out of
    /// the fixed order (`#requires` < `#ensures` < `#decreases` <
    /// `#backed-by` < `#effects`), a second `#backed-by` and a second
    /// `#effects`.
    fn parse_summary_directive<X>(
        &mut self,
        func: &mut FunctionG<X>,
        state: SummaryBlock,
        phase: u8,
    ) -> Result<SummaryBlock, ParseError> {
        let word = SummaryBlock::word(phase);
        if phase == SummaryBlock::HEADER {
            if !matches!(state, SummaryBlock::NotStarted) {
                return Err(self.error("duplicate #summary directive"));
            }
            let proved = match self.read_ident()?.as_str() {
                "proved" => true,
                "unproved" => false,
                other => {
                    return Err(self.error(format!(
                        "expected `proved` or `unproved` after #summary, got '{other}'"
                    )));
                }
            };
            self.expect_str("params")?;
            let params = self.parse_string_list()?;
            func.summary = Some(FunctionSummary {
                proved,
                params,
                ..FunctionSummary::default()
            });
            return Ok(SummaryBlock::Open(phase));
        }
        let current = match state {
            SummaryBlock::NotStarted => {
                return Err(
                    self.error(format!("`{word}` without a preceding `#summary` directive"))
                );
            }
            SummaryBlock::Closed => {
                return Err(self.error(format!(
                    "`{word}` after the summary block ended — the #summary block is one \
                     contiguous run"
                )));
            }
            SummaryBlock::Open(current) => current,
        };
        if phase < current {
            return Err(self.error(format!(
                "`{word}` out of order in the #summary block (#requires, #ensures, #decreases, \
                 #backed-by, then #effects)"
            )));
        }
        let summary = func
            .summary
            .as_mut()
            .expect("an open summary block has a summary");
        match phase {
            SummaryBlock::REQUIRES => summary.requires.push(self.parse_proof_formula()?),
            SummaryBlock::ENSURES => summary.ensures.push(self.parse_proof_formula()?),
            SummaryBlock::DECREASES => summary.decreases.push(self.parse_proof_formula()?),
            SummaryBlock::BACKED_BY => {
                if phase == current {
                    return Err(self.error("duplicate #backed-by directive"));
                }
                self.expect_str("extern")?;
                summary.backed_by = Some(self.parse_extern_ref_tail()?);
            }
            _ => {
                if phase == current {
                    return Err(self.error("duplicate #effects directive"));
                }
                summary.effects = Some(self.parse_effect_summary()?);
            }
        }
        Ok(SummaryBlock::Open(phase))
    }

    /// Parse a v32 `; #names:` payload. Names are Debug-quoted strings so
    /// producer text containing commas, whitespace, or escapes remains
    /// unambiguous.
    fn parse_value_names(&mut self) -> Result<Vec<(ValueId, String)>, ParseError> {
        let mut names = Vec::new();
        loop {
            self.skip_whitespace_no_newline();
            if self.peek_char().is_none_or(|c| c == '\n') {
                return Ok(names);
            }
            let value = self.read_value_id()?;
            self.skip_whitespace_no_newline();
            if !self.remaining().starts_with('=') {
                return Err(self.error("expected '=' after value id in #names directive"));
            }
            self.bump();
            let name = self.read_quoted_string()?;
            names.push((value, name));

            self.skip_whitespace_no_newline();
            match self.peek_char() {
                Some(',') => {
                    self.bump();
                }
                None | Some('\n') => return Ok(names),
                Some(other) => {
                    return Err(self.error(format!(
                        "expected ',' or end of line after #names entry, got '{other}'"
                    )));
                }
            }
        }
    }

    /// Parse one v33 function-level `; #scope:` tree entry.
    fn parse_scope_data(&mut self) -> Result<(u32, ScopeData), ParseError> {
        let index = self.read_u32()?;
        self.skip_whitespace_no_newline();
        let parent = if self.remaining().starts_with("root") {
            self.advance("root".len())?;
            None
        } else if self.remaining().starts_with("parent=") {
            self.advance("parent=".len())?;
            Some(self.read_u32()?)
        } else {
            return Err(self.error("expected 'root' or 'parent=<index>' in #scope directive"));
        };

        self.skip_whitespace_no_newline();
        let span = if self.remaining().starts_with("at") {
            self.advance("at".len())?;
            Some(self.parse_loc_clause()?)
        } else {
            None
        };
        self.skip_whitespace_no_newline();
        // WS4.19: `inlined-at <file> <line> <col> callee "<path>"`. Both halves
        // are required — a link without its callee is refused here, not
        // decoded with a placeholder.
        let inlined_at = if self.remaining().starts_with("inlined-at") {
            self.advance("inlined-at".len())?;
            let call_site = self.parse_loc_clause()?;
            self.skip_whitespace_no_newline();
            if !self.remaining().starts_with("callee") {
                return Err(
                    self.error("expected 'callee \"<path>\"' after inlined-at in #scope directive")
                );
            }
            self.advance("callee".len())?;
            self.skip_whitespace_no_newline();
            let callee = self.read_quoted_string()?;
            Some(InlinedAt {
                span: call_site,
                callee,
            })
        } else {
            None
        };
        self.skip_whitespace_no_newline();
        if self.peek_char().is_some_and(|c| c != '\n') {
            return Err(self.error("unexpected trailing text in #scope directive"));
        }
        Ok((
            index,
            ScopeData {
                parent,
                span,
                inlined_at,
            },
        ))
    }

    /// Parse the payload of a `; #producer:` directive (v23): a bare token
    /// from the stable vocabulary (`trust`, `clean`, `trust-ir`, `tswift`,
    /// `tc`) or a quoted string for the [`Producer::Other`] escape. A quoted
    /// known token (e.g. `"trust"`) stays `Other`, so `Other("trust")` and
    /// `TRust` round-trip distinctly.
    fn parse_producer(&mut self) -> Result<Producer, ParseError> {
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with('"') {
            return Ok(Producer::Other(self.read_quoted_string()?));
        }
        // `trust-ir` contains `-`, which `read_ident` stops at — match the
        // known tokens by delimited prefix instead. Longest first so `trust`
        // does not shadow `trust-ir`.
        let rest = self.remaining();
        const TOKENS: [(&str, Producer); 5] = [
            ("trust-ir", Producer::TrustIr),
            ("trust", Producer::TRust),
            ("tswift", Producer::TSwift),
            ("clean", Producer::Clean),
            ("tc", Producer::TC),
        ];
        for (tok, producer) in TOKENS {
            let delimited = rest.strip_prefix(tok).is_some_and(|after| {
                !after
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '-')
            });
            if delimited {
                self.advance(tok.len())?;
                return Ok(producer);
            }
        }
        Err(self
            .error("expected producer token (trust, clean, trust-ir, tswift, tc) or quoted string"))
    }

    /// Parse the `; #body-gate:` clause (v41): the bare token `ungated`, or
    /// `gated` followed by a quoted authority, optionally followed (v61) by
    /// `evidence #<obligation> "<algorithm>:<hex>"` — the license's
    /// [`crate::GateEvidence`], spelled exactly as `BodyGate`'s `Display`
    /// prints it.
    ///
    /// There is deliberately NO spelling for `None` here — an absent directive
    /// IS `None`. Giving "no claim" a token would let a text round-trip turn
    /// the grandfather state into an affirmative one.
    fn parse_body_gate(&mut self) -> Result<crate::BodyGate, ParseError> {
        self.skip_whitespace_no_newline();
        let rest = self.remaining();
        let delimited = |tok: &str| {
            rest.strip_prefix(tok).is_some_and(|after| {
                !after
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '-')
            })
        };
        if delimited("ungated") {
            self.advance("ungated".len())?;
            return Ok(crate::BodyGate::Ungated);
        }
        if delimited("gated") {
            self.advance("gated".len())?;
            self.skip_whitespace_no_newline();
            let authority = self.read_quoted_string()?;
            self.skip_whitespace_no_newline();
            let evidence = if self.remaining().starts_with("evidence") {
                self.advance("evidence".len())?;
                self.skip_whitespace_no_newline();
                if !self.remaining().starts_with('#') {
                    return Err(self.error("expected `#<obligation>` after `evidence`"));
                }
                self.advance(1)?;
                let obligation = crate::ProofId::new(self.read_u32()?);
                self.skip_whitespace_no_newline();
                let body_digest = self.read_source_provenance_digest()?;
                Some(crate::GateEvidence {
                    obligation,
                    body_digest,
                })
            } else {
                None
            };
            return Ok(crate::BodyGate::Gated {
                authority,
                evidence,
            });
        }
        Err(self.error("expected body gate (`ungated`, or `gated \"<authority>\"`)"))
    }

    /// Parse the function-level attribute flags on a `; #attrs:` line: a
    /// space-separated subset of `readonly readnone inlinehint cold` until the
    /// end of the line (finding B).
    fn parse_func_attr_flags(&mut self, attrs: &mut crate::FuncAttrs) -> Result<(), ParseError> {
        loop {
            self.skip_whitespace_no_newline();
            if self.peek_char().is_none_or(|c| c == '\n') {
                break;
            }
            let flag = self.read_ident()?;
            match flag.as_str() {
                "readonly" => attrs.readonly = true,
                "readnone" => attrs.readnone = true,
                "inlinehint" => attrs.inlinehint = true,
                "cold" => attrs.cold = true,
                "naked" => attrs.naked = true,
                other => return Err(self.error(format!("unknown function attr: '{}'", other))),
            }
        }
        Ok(())
    }

    /// Parse a `; #param_attrs N: ...` line into `attrs.params[N]` (finding B).
    /// The `params` vector is grown to length `N+1` with default entries so the
    /// positional contract is preserved even when only some params carry attrs.
    fn parse_param_attrs(&mut self, attrs: &mut crate::FuncAttrs) -> Result<(), ParseError> {
        let idx = self.read_u32()? as usize;
        self.expect_char(':')?;
        let pa = self.parse_slot_attrs()?;
        if attrs.params.len() <= idx {
            attrs.params.resize(idx + 1, crate::ParamAttrs::default());
        }
        attrs.params[idx] = pa;
        Ok(())
    }

    /// One slot's attribute list, shared by `#param_attrs N:` and the v45
    /// `#ret_attrs:` line.
    fn parse_slot_attrs(&mut self) -> Result<crate::ParamAttrs, ParseError> {
        let mut pa = crate::ParamAttrs::default();
        loop {
            self.skip_whitespace_no_newline();
            if self.peek_char().is_none_or(|c| c == '\n') {
                break;
            }
            let tok = self.read_ident()?;
            match tok.as_str() {
                "dereferenceable" => {
                    self.expect_char('(')?;
                    pa.dereferenceable = Some(self.read_u64()?);
                    self.expect_char(')')?;
                }
                "nonnull" => pa.nonnull = true,
                "align" => {
                    self.expect_char('(')?;
                    pa.align = Some(self.read_u64()?);
                    self.expect_char(')')?;
                }
                "noalias" => pa.noalias = true,
                "readonly" => pa.readonly = true,
                "byval" => pa.byval = true,
                "sret" => pa.sret = true,
                // v45 (WS3.11). An extension and a pass mode are each stated
                // at most once per slot: `zeroext signext` is not a third
                // extension and `pass=pair pass=direct` is not a correction —
                // the binary reader refuses both extension bits set, and the
                // text form refuses the same contradiction instead of letting
                // the later token win (review).
                "zeroext" | "signext" => {
                    if pa.ext != crate::ArgExt::None {
                        return Err(self.error(format!(
                            "`{tok}` restates the slot's extension (already `{}`)",
                            pa.ext.token().unwrap_or("none")
                        )));
                    }
                    pa.ext = if tok == "zeroext" {
                        crate::ArgExt::ZeroExt
                    } else {
                        crate::ArgExt::SignExt
                    };
                }
                "pass" => {
                    if let Some(prior) = &pa.pass {
                        return Err(self.error(format!(
                            "`pass` restates the slot's pass mode (already `{}`)",
                            prior.token()
                        )));
                    }
                    self.expect_char('=')?;
                    let mode = self.read_ident()?;
                    pa.pass = Some(match mode.as_str() {
                        "ignore" => crate::PassMode::Ignore,
                        "direct" => crate::PassMode::Direct,
                        "pair" => crate::PassMode::Pair,
                        "cast" => {
                            self.expect_char('(')?;
                            let mut pieces = vec![self.parse_ty()?];
                            while self.try_str(",") {
                                pieces.push(self.parse_ty()?);
                            }
                            self.expect_char(')')?;
                            crate::PassMode::Cast { pieces }
                        }
                        "indirect" => {
                            self.expect_char('(')?;
                            let flag = self.read_ident()?;
                            let on_stack = match flag.as_str() {
                                "true" => true,
                                "false" => false,
                                other => {
                                    return Err(self.error(format!(
                                        "expected `true`/`false` for `indirect`, got '{other}'"
                                    )));
                                }
                            };
                            self.expect_char(')')?;
                            crate::PassMode::Indirect { on_stack }
                        }
                        other => {
                            return Err(self.error(format!("unknown pass mode: '{other}'")));
                        }
                    });
                }
                other => return Err(self.error(format!("unknown param attr: '{}'", other))),
            }
        }
        Ok(pa)
    }

    /// Parse a struct definition: struct.N @Name { TY, TY, ... } [size=N] [align=N]
    ///
    /// The explicit `struct.N` id preserves the original `StructId` so that
    /// `Ty::Struct(id)` references survive even when ids are sparse (finding E).
    /// Parse a struct definition:
    /// `struct @Name { TY, TY, ... } [size=N] [align=N] id=N`
    ///
    /// The trailing `id=N` preserves the original `StructId` so `Ty::Struct(id)`
    /// references survive even when ids are sparse (finding E). Emitting the id
    /// as a trailer keeps the human-readable `struct @Name { .. }` prefix.
    /// WS4.5 (struct half): one struct field, in either spelling.
    ///
    /// CANONICAL: `name: ty` with an optional ` @offset`. The name goes through
    /// [`Self::read_symbol`], so a field name outside the bare alphabet is
    /// quoted exactly like a definition-site name.
    ///
    /// LEGACY, still accepted on read: a bare `ty` with no name and no offset,
    /// which is what every pre-WS4.5 text says. It means name `""` and
    /// `offset: None` — the same module the old parser built — so old text keeps
    /// parsing to the same thing. It is NOT a canonical spelling and is never
    /// printed, so the one-spelling rule still holds on printer OUTPUT.
    ///
    /// The two are told apart without backtracking: a canonical field always has
    /// a `:` after its name, and a type never contains a top-level `:`.
    fn parse_struct_field(&mut self) -> Result<FieldDef, ParseError> {
        self.skip_whitespace();
        if self.struct_field_is_named() {
            // A leading `:` is the EMPTY-name spelling (`: ty @off`), the only
            // way to carry an offset on an unnamed field.
            let name = if self.remaining().starts_with(':') {
                String::new()
            } else {
                self.read_symbol()?
            };
            self.skip_whitespace();
            self.expect_char(':')?;
            let ty = self.parse_ty()?;
            self.skip_whitespace_no_newline();
            let offset = if self.remaining().starts_with('@') {
                self.expect_char('@')?;
                Some(self.read_u64()?)
            } else {
                None
            };
            return Ok(FieldDef { name, ty, offset });
        }
        let ty = self.parse_ty()?;
        Ok(FieldDef {
            name: String::new(),
            ty,
            offset: None,
        })
    }

    /// Does the field at the cursor use the canonical `name: ty` spelling?
    /// Scans the bare-identifier run (or a quoted name) and asks whether the
    /// next non-space character is `:`. Pure lookahead — the cursor does not
    /// move.
    fn struct_field_is_named(&self) -> bool {
        let rest = self.remaining();
        let mut it = rest.char_indices().skip_while(|(_, c)| c.is_whitespace());
        let Some((start, first)) = it.next() else {
            return false;
        };
        if first == ':' {
            // The empty-name spelling.
            return true;
        }
        let after = if first == '"' {
            // Quoted name: find the closing quote, honouring `\\` escapes.
            let mut idx = None;
            let mut escaped = false;
            for (i, c) in rest[start + 1..].char_indices() {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    idx = Some(start + 1 + i + 1);
                    break;
                }
            }
            match idx {
                Some(i) => i,
                None => return false,
            }
        } else {
            let mut end = start;
            for (i, c) in rest[start..].char_indices() {
                if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$' {
                    end = start + i + c.len_utf8();
                } else {
                    break;
                }
            }
            if end == start {
                return false;
            }
            end
        };
        rest[after..].trim_start().starts_with(':')
    }

    fn parse_struct_def(&mut self) -> Result<StructDef, ParseError> {
        self.expect_str("struct")?;
        self.expect_char('@')?;
        let name = self.read_symbol()?;
        self.expect_char('{')?;

        let mut fields = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with('}') {
            fields.push(self.parse_struct_field()?);
            while self.try_str(",") {
                self.skip_whitespace();
                if self.remaining().starts_with('}') {
                    break;
                }
                fields.push(self.parse_struct_field()?);
            }
        }
        self.expect_char('}')?;

        let mut size = None;
        let mut align = None;
        // Optional size=N and align=N
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("size=") {
            self.advance(5)?;
            size = Some(self.read_u64()?);
        }
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("align=") {
            self.advance(6)?;
            align = Some(self.read_u64()?);
        }
        // Optional ABI repr (`repr=c` / `repr=transparent` / `repr=packed(N)`);
        // absent means the default Rust repr.
        let mut repr = crate::ty::StructRepr::Rust;
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("repr=") {
            self.advance(5)?;
            let kind = self.read_ident()?;
            repr = match kind.as_str() {
                "rust" => crate::ty::StructRepr::Rust,
                "c" => crate::ty::StructRepr::C,
                "transparent" => crate::ty::StructRepr::Transparent,
                "packed" => {
                    self.expect_char('(')?;
                    let align = self.read_u32()?;
                    self.expect_char(')')?;
                    crate::ty::StructRepr::Packed(align)
                }
                other => return Err(self.error(format!("unknown struct repr: '{other}'"))),
            };
        }
        // v58 nominal identity key (`origin=rust(..)` / `origin=clean(..)`),
        // absent for an unkeyed definition.
        let origin = self.parse_type_origin_clause()?;
        // Explicit id trailer (finding E). Required by the current writer;
        // accepted optionally so older id-less text still parses (ids then
        // fall back to positional, the historical behavior).
        let id = self.parse_struct_kind_id_trailer()?;

        Ok(StructDef {
            id: StructId::new(id),
            name,
            fields,
            size,
            align,
            repr,
            origin,
        })
    }

    /// Parse the optional v58 nominal identity clause printed between a
    /// definition's body and its `id=N` trailer:
    ///
    /// ```text
    /// origin=rust(crate=0x…, path=<32 hex>, args=sha256:<64 hex>)
    /// origin=clean(decl="Nat", env=sha256:<64 hex>)
    /// ```
    ///
    /// Absence parses to `None` — the state every pre-v58 definition is in.
    /// It is never inferred from anything else in the text.
    fn parse_type_origin_clause(&mut self) -> Result<Option<crate::ty::TypeOrigin>, ParseError> {
        self.skip_whitespace_no_newline();
        if !self.remaining().starts_with("origin=") {
            return Ok(None);
        }
        self.advance(7)?;
        let kind = self.read_ident()?;
        self.expect_char('(')?;
        let origin = match kind.as_str() {
            "rust" => {
                self.expect_str("crate=")?;
                let stable_crate_id = self.read_hex_u64()?;
                self.expect_char(',')?;
                self.skip_whitespace();
                self.expect_str("path=")?;
                let def_path_hash = self.read_hex_bytes::<16>()?;
                self.expect_char(',')?;
                self.skip_whitespace();
                self.expect_str("args=")?;
                let args_digest = self.read_digest_text()?;
                crate::ty::TypeOrigin::Rust {
                    stable_crate_id,
                    def_path_hash,
                    args_digest,
                }
            }
            "clean" => {
                self.expect_str("decl=")?;
                let decl = self.read_quoted_string()?;
                self.expect_char(',')?;
                self.skip_whitespace();
                self.expect_str("env=")?;
                let env_digest = self.read_digest_text()?;
                crate::ty::TypeOrigin::Clean { decl, env_digest }
            }
            other => return Err(self.error(format!("unknown type origin: '{other}'"))),
        };
        self.expect_char(')')?;
        Ok(Some(origin))
    }

    /// `0x`-prefixed, zero-padded 64-bit hex, as `TypeOrigin`'s display writes
    /// a `StableCrateId`.
    fn read_hex_u64(&mut self) -> Result<u64, ParseError> {
        self.expect_str("0x")?;
        let bytes = self.read_hex_bytes::<8>()?;
        Ok(u64::from_be_bytes(bytes))
    }

    /// Exactly `2 * N` lowercase hex digits. A short or over-long run is a
    /// parse error rather than a silent truncation: these are identity bytes.
    fn read_hex_bytes<const N: usize>(&mut self) -> Result<[u8; N], ParseError> {
        let mut out = [0u8; N];
        for byte in &mut out {
            let hi = self.read_hex_digit()?;
            let lo = self.read_hex_digit()?;
            *byte = (hi << 4) | lo;
        }
        Ok(out)
    }

    /// One LOWERCASE hex digit (`0-9a-f`), the only case
    /// [`crate::ty::TypeOrigin`]'s display and [`crate::ty::DigestText`]
    /// write. An identity key has one text spelling: an uppercase digit is
    /// refused, not folded, so a hand-edited key cannot pass for the one a
    /// producer printed (`docs/SPEC_RATIFICATIONS.md` §3, one spelling per
    /// construct).
    fn read_hex_digit(&mut self) -> Result<u8, ParseError> {
        let Some(c) = self.remaining().chars().next() else {
            return Err(self.error("expected a lowercase hex digit"));
        };
        let value = match c {
            '0'..='9' => c as u8 - b'0',
            'a'..='f' => c as u8 - b'a' + 10,
            _ => {
                return Err(self.error(format!("expected a lowercase hex digit, found '{c}'")));
            }
        };
        self.advance(c.len_utf8())?;
        Ok(value)
    }

    /// `sha256:<64 hex>` / `stablev1:<64 hex>` — the one spelling
    /// [`crate::ty::DigestText`] prints.
    fn read_digest_text(&mut self) -> Result<crate::proof::ProofDigest, ParseError> {
        let algorithm = if self.try_str("sha256:") {
            crate::proof::ProofDigestAlgorithm::Sha256
        } else if self.try_str("stablev1:") {
            crate::proof::ProofDigestAlgorithm::TrustIrStableV1
        } else {
            return Err(self.error("expected 'sha256:' or 'stablev1:' before a digest"));
        };
        Ok(crate::proof::ProofDigest {
            algorithm,
            bytes: self.read_hex_bytes::<32>()?,
        })
    }

    /// Parse the trailing `id=N` clause emitted after struct/enum/record
    /// definitions (finding E). Defaults to the current table length when
    /// absent (back-compat with id-less text): the caller appends in order, so
    /// the table length is the positional id.
    fn parse_struct_kind_id_trailer(&mut self) -> Result<u32, ParseError> {
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("id=") {
            self.advance(3)?;
            self.read_u32()
        } else {
            // No explicit id: signal "use positional" via u32::MAX sentinel is
            // brittle; instead error so the writer/reader stay in lockstep. The
            // writer always emits an id, so reaching here means malformed text.
            Err(self.error("expected 'id=N' trailer on type definition"))
        }
    }

    /// Read an enum tag-representation width (`u8` .. `i64`, and the v45
    /// 128-bit lanes). Shared by the `repr(..)` hint and the `layout(..)`
    /// clause's niche `lane=<repr>@<offset>`, so the two cannot drift.
    fn read_enum_tag_repr(&mut self) -> Result<crate::ty::EnumTagRepr, ParseError> {
        let width = self.read_ident()?;
        Ok(match width.as_str() {
            "u8" => crate::ty::EnumTagRepr::U8,
            "u16" => crate::ty::EnumTagRepr::U16,
            "u32" => crate::ty::EnumTagRepr::U32,
            "u64" => crate::ty::EnumTagRepr::U64,
            "i8" => crate::ty::EnumTagRepr::I8,
            "i16" => crate::ty::EnumTagRepr::I16,
            "i32" => crate::ty::EnumTagRepr::I32,
            "i64" => crate::ty::EnumTagRepr::I64,
            // v45 (WS3.14(b)): 128-bit tag lanes.
            "u128" => crate::ty::EnumTagRepr::U128,
            "i128" => crate::ty::EnumTagRepr::I128,
            other => {
                return Err(self.error(format!("invalid enum tag repr: '{other}'")));
            }
        })
    }

    /// WS4.5 (enum half): the `layout(..)` clause of an enum definition — the
    /// producer's concrete [`crate::ty::EnumLayoutDescriptor`], which is
    /// NORMATIVE where present. Mirrors `display::write_enum_layout`; the
    /// cursor is just past `layout`.
    ///
    /// Every field is read from the text. Nothing is defaulted and nothing is
    /// inferred: a missing key, an unknown encoding word or a malformed
    /// integer is a located `ParseError`, because a descriptor that is
    /// partially read is a layout a consumer would then USE — the false-PROVE
    /// direction. Internal consistency against the enum itself (one offset
    /// list per variant, one offset per field, lanes and offsets inside the
    /// declared size, a niche interval that names real variants, an
    /// `Untagged` image with one variant) is checked by
    /// `text_loss::enum_layout_text_refusal` once the variants are known —
    /// the same authority that decides whether the printer may spell it at
    /// all.
    fn parse_enum_layout(&mut self) -> Result<crate::ty::EnumLayoutDescriptor, ParseError> {
        use crate::ty::{EnumLayoutDescriptor, EnumTagEncoding};
        self.expect_char('(')?;
        let encoding = if self.try_str("direct") {
            self.expect_str("tag")?;
            self.expect_char('@')?;
            EnumTagEncoding::Direct {
                tag_offset: self.read_u64()?,
            }
        } else if self.try_str("niche") {
            self.expect_str("untagged")?;
            self.expect_char('=')?;
            let untagged_variant = self.read_u32()?;
            self.expect_str("variants")?;
            self.expect_char('=')?;
            let niche_variants_start = self.read_u32()?;
            self.expect_str("..=")?;
            let niche_variants_end = self.read_u32()?;
            self.expect_str("start")?;
            self.expect_char('=')?;
            let niche_start = self.read_u128()?;
            self.expect_str("lane")?;
            self.expect_char('=')?;
            let niche_ty = self.read_enum_tag_repr()?;
            self.expect_char('@')?;
            let niche_offset = self.read_u64()?;
            EnumTagEncoding::Niche {
                untagged_variant,
                niche_variants_start,
                niche_variants_end,
                niche_start,
                niche_offset,
                niche_ty,
            }
        } else if self.try_str("untagged") {
            EnumTagEncoding::Untagged
        } else if self.try_str("single") {
            self.expect_str("inhabited")?;
            self.expect_char('=')?;
            EnumTagEncoding::SingleInhabited {
                variant: self.read_u32()?,
            }
        } else {
            return Err(self.error(
                "expected an enum layout encoding: 'direct', 'niche', 'untagged' or 'single'",
            ));
        };
        self.expect_str("size")?;
        self.expect_char('=')?;
        let size = self.read_u64()?;
        self.expect_str("align")?;
        self.expect_char('=')?;
        let align = self.read_u64()?;
        self.expect_str("offsets")?;
        self.expect_char('=')?;
        self.expect_char('[')?;
        let mut variant_field_offsets: Vec<Vec<u64>> = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with(']') {
            loop {
                self.expect_char('[')?;
                let mut offsets = Vec::new();
                self.skip_whitespace();
                if !self.remaining().starts_with(']') {
                    offsets.push(self.read_u64()?);
                    while self.try_str(",") {
                        offsets.push(self.read_u64()?);
                    }
                }
                self.expect_char(']')?;
                variant_field_offsets.push(offsets);
                if !self.try_str(",") {
                    break;
                }
            }
        }
        self.expect_char(']')?;
        self.expect_char(')')?;
        Ok(EnumLayoutDescriptor {
            encoding,
            size,
            align,
            variant_field_offsets,
        })
    }

    /// Parse an enum definition:
    /// `enum @Name [repr(u8)] { Variant1 [= N], Variant2(TY, TY) [= N], ... } [layout(..)] id=N`
    ///
    /// The optional `repr(..)` hint and per-variant `= N` explicit
    /// discriminants mirror `Display for Module`; when absent the historical
    /// all-implicit form parses to an empty `discriminants` vector (the
    /// canonical trimmed form: trailing implicit entries are not stored).
    fn parse_enum_def(&mut self) -> Result<EnumDef, ParseError> {
        self.expect_str("enum")?;
        self.expect_char('@')?;
        let name = self.read_symbol()?;
        self.skip_whitespace();
        let mut repr = None;
        if self.try_str("repr") {
            self.expect_char('(')?;
            self.skip_whitespace();
            repr = Some(self.read_enum_tag_repr()?);
            self.skip_whitespace();
            self.expect_char(')')?;
        }
        self.expect_char('{')?;

        let mut variants = Vec::new();
        let mut discriminants: Vec<Option<i128>> = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with('}') {
            loop {
                self.skip_whitespace();
                if self.remaining().starts_with('}') {
                    break;
                }
                let variant_name = self.read_symbol()?;
                let mut fields = Vec::new();
                // WS4.5: per-field names, `Name(field: ty, ..)`. `Some` once
                // the first field fixed the variant's spelling as NAMED,
                // `None` while positional; a variant that mixes the two is
                // REFUSED (one spelling per construct), never half-read.
                let mut field_names: Option<Vec<String>> = None;
                if self.try_str("(") && !self.try_str(")") {
                    loop {
                        let named = self.struct_field_is_named();
                        if fields.is_empty() {
                            if named {
                                field_names = Some(Vec::new());
                            }
                        } else if named != field_names.is_some() {
                            return Err(self.error(format!(
                                "enum variant `{variant_name}` mixes named (`field: ty`) and \
                                 positional fields — a variant is spelled all-named or \
                                 all-positional"
                            )));
                        }
                        if let Some(names) = field_names.as_mut() {
                            self.skip_whitespace();
                            // A leading `:` is the EMPTY-name spelling.
                            let name = if self.remaining().starts_with(':') {
                                String::new()
                            } else {
                                self.read_symbol()?
                            };
                            self.skip_whitespace();
                            self.expect_char(':')?;
                            names.push(name);
                        }
                        fields.push(self.parse_ty()?);
                        if !self.try_str(",") {
                            break;
                        }
                        self.skip_whitespace();
                        // Check if next is ')' (trailing comma)
                        if self.remaining().starts_with(')') {
                            break;
                        }
                    }
                    self.expect_char(')')?;
                }
                // Optional explicit discriminant: `= N`. Implicit variants
                // store nothing (trimmed form), so `discriminants` is padded
                // with `None` up to this variant's index only when needed.
                if self.try_str("=") {
                    self.skip_whitespace();
                    discriminants.resize(variants.len(), None);
                    discriminants.push(Some(self.read_i128()?));
                }
                variants.push(EnumVariant {
                    name: variant_name,
                    fields,
                    field_names: field_names.unwrap_or_default(),
                });
                if !self.try_str(",") {
                    break;
                }
            }
        }
        self.expect_char('}')?;
        // WS4.5 (enum half): the optional `layout(..)` clause, bound to this
        // definition's LINE exactly as the `id=N` trailer is — so a `layout`
        // word on a following line is not silently adopted.
        self.skip_whitespace_no_newline();
        let layout = if self.remaining().starts_with("layout(") {
            self.advance("layout".len())?;
            Some(self.parse_enum_layout()?)
        } else {
            None
        };
        let origin = self.parse_type_origin_clause()?;
        let id = self.parse_struct_kind_id_trailer()?;

        let def = EnumDef {
            id: EnumId::new(id),
            name,
            variants,
            discriminants,
            repr,
            layout,
            origin,
        };
        // REFUSE, never default: a descriptor that does not fit its own enum
        // is a parse error. `enum_layout_text_refusal` is the same authority
        // the printer consults, so every clause the printer writes is accepted
        // here and every one it refuses to write is rejected here.
        if let Some(reason) = crate::text_loss::enum_layout_text_refusal(&def) {
            return Err(self.error(format!("{reason} (enum @{})", def.name)));
        }
        Ok(def)
    }

    /// Parse a record definition: record @Name { field: TY, field: TY } id=N
    fn parse_record_def(&mut self) -> Result<crate::ty::RecordDef, ParseError> {
        self.expect_str("record")?;
        self.expect_char('@')?;
        let name = self.read_symbol()?;
        self.skip_whitespace();
        self.expect_char('{')?;

        let mut fields = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with('}') {
            loop {
                self.skip_whitespace();
                if self.remaining().starts_with('}') {
                    break;
                }
                let field_name = self.read_symbol()?;
                self.skip_whitespace();
                self.expect_char(':')?;
                let ty = self.parse_ty()?;
                fields.push(FieldDef {
                    name: field_name,
                    ty,
                    offset: None,
                });
                self.skip_whitespace();
                if !self.try_str(",") {
                    break;
                }
            }
        }
        self.skip_whitespace();
        self.expect_char('}')?;
        let id = self.parse_struct_kind_id_trailer()?;

        Ok(crate::ty::RecordDef {
            id: RecordId::new(id),
            name,
            fields,
        })
    }

    /// Parse a closure type definition: closure_ty functy.N { Ty, Ty, ... }
    fn parse_closure_ty_def(&mut self) -> Result<crate::ty::ClosureTy, ParseError> {
        self.expect_str("closure_ty")?;
        self.skip_whitespace();
        self.expect_str("functy.")?;
        let func_id = self.read_u32()?;
        self.skip_whitespace();
        self.expect_char('{')?;

        let mut captures = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with('}') {
            captures.push(self.parse_ty()?);
            while self.try_str(",") {
                self.skip_whitespace();
                if self.remaining().starts_with('}') {
                    break;
                }
                captures.push(self.parse_ty()?);
            }
        }
        self.skip_whitespace();
        self.expect_char('}')?;

        Ok(crate::ty::ClosureTy {
            func: FuncTyId::new(func_id),
            captures,
        })
    }

    fn parse_ty_list<X: ParseExt>(&mut self) -> Result<Vec<TyG<X>>, ParseError> {
        self.expect_char('(')?;
        let mut tys = Vec::new();
        self.skip_whitespace();
        if self.try_str(")") {
            return Ok(tys);
        }

        loop {
            tys.push(self.parse_ty()?);
            self.skip_whitespace();
            if !self.try_str(",") {
                break;
            }
            self.skip_whitespace();
            if self.remaining().starts_with(')') {
                break;
            }
        }
        self.expect_char(')')?;
        Ok(tys)
    }

    fn parse_func_ty_params<X: ParseExt>(&mut self) -> Result<(Vec<TyG<X>>, bool), ParseError> {
        self.expect_char('(')?;
        let mut params = Vec::new();
        let mut is_vararg = false;
        self.skip_whitespace();
        if self.try_str(")") {
            return Ok((params, is_vararg));
        }

        loop {
            self.skip_whitespace();
            if self.remaining().starts_with("...") {
                self.advance(3)?;
                is_vararg = true;
                self.skip_whitespace();
                self.expect_char(')')?;
                return Ok((params, is_vararg));
            }

            params.push(self.parse_ty()?);
            self.skip_whitespace();
            if !self.try_str(",") {
                break;
            }
            self.skip_whitespace();
            if self.remaining().starts_with(')') {
                break;
            }
        }

        self.expect_char(')')?;
        Ok((params, is_vararg))
    }

    /// Parse a module `types` table entry: `type ty.N = <Ty>` (finding A).
    /// Returns the declared index and the type so the caller can enforce dense
    /// ordering (`TyId` is positional into `module.types`).
    /// Parse a v41 cross-crate import entry:
    /// `import import.N = "name" digest "sha256" [b, ...] [producer <p>] [scheme v3]`
    /// (the `scheme` clause is v44; its absence is the legacy V2).
    ///
    /// Returns the declared index so the caller can enforce dense ordering —
    /// an `ImportId` is positional into `module.imports`, so a gap silently
    /// re-points every later `ExternRef`.
    fn parse_module_import(&mut self) -> Result<(u32, crate::ModuleImport), ParseError> {
        self.expect_str("import")?;
        self.expect_str("import.")?;
        let id = self.read_u32()?;
        self.expect_char('=')?;
        let name = self.read_quoted_string()?;
        self.expect_str("digest")?;
        let algorithm = match self.read_quoted_string()?.as_str() {
            "sha256" => ProofDigestAlgorithm::Sha256,
            "trust_ir-stable-v1" => ProofDigestAlgorithm::TrustIrStableV1,
            other => {
                return Err(self.error(format!("unknown proof digest algorithm: '{}'", other)));
            }
        };
        let bytes = self.parse_hash_array()?;
        // Same-line only: the next module statement is on the following line
        // and `producer` is never its first token today, but relying on that
        // would be one keyword away from a silent misparse.
        self.skip_whitespace_no_newline();
        let producer = if self.remaining().starts_with("producer ") {
            self.advance(9)?;
            Some(self.parse_producer()?)
        } else {
            None
        };
        // v44: ` scheme v3`. V2 is spelled by OMISSION (one spelling per
        // construct), so an explicit `scheme v2` is refused rather than
        // accepted as a second spelling.
        self.skip_whitespace_no_newline();
        let scheme = if self.remaining().starts_with("scheme ") {
            self.advance(7)?;
            // The label is a DELIMITED token (the `parse_producer` rule): a
            // `v3x` must be refused, never read as `v3` plus ignored bytes.
            let label_is = |rest: &str, label: &str| {
                rest.strip_prefix(label).is_some_and(|after| {
                    !after
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '-')
                })
            };
            if label_is(self.remaining(), "v3") {
                self.advance(2)?;
                crate::IdentityScheme::V3
            } else if label_is(self.remaining(), "v2") {
                return Err(self.error(
                    "import scheme v2 is spelled by omitting the `scheme` clause".to_string(),
                ));
            } else {
                return Err(
                    self.error("unknown import identity scheme (expected `v3`)".to_string())
                );
            }
        } else {
            crate::IdentityScheme::V2
        };
        // The entry must END here (a `;` comment aside). The module loop skips
        // a line it does not recognize, so without this an unknown token
        // between the clauses (`producer trust junk scheme v3`) would drop the
        // `scheme` clause SILENTLY and read a V3 row as V2 — a row that then
        // authenticates under the wrong identity domain.
        self.skip_whitespace_no_newline();
        let rest = self.remaining();
        if !(rest.is_empty()
            || rest.starts_with('\n')
            || rest.starts_with("\r\n")
            || rest.starts_with(';'))
        {
            return Err(self.error(format!(
                "unexpected text after import entry: '{}'",
                rest.lines().next().unwrap_or_default()
            )));
        }
        Ok((
            id,
            crate::ModuleImport {
                name,
                digest: ProofDigest { algorithm, bytes },
                producer,
                scheme,
            },
        ))
    }

    /// Parse a universe table entry: `univ univ.N = 1..=8` or
    /// `univ univ.N = {1, 2, 3}`. The spelling mirrors `Display for Universe`
    /// exactly so a module round-trips through text unchanged.
    fn parse_universe_def(&mut self) -> Result<(u32, crate::pred::Universe), ParseError> {
        self.expect_str("univ")?;
        self.expect_str("univ.")?;
        let id = self.read_u32()?;
        self.expect_char('=')?;
        self.skip_whitespace();
        if self.remaining().starts_with('{') {
            self.bump();
            self.skip_whitespace();
            let mut items = Vec::new();
            if !self.try_str("}") {
                items.push(self.parse_constant()?);
                while self.try_str(",") {
                    items.push(self.parse_constant()?);
                }
                self.expect_str("}")?;
            }
            // Deliberately NOT canonicalized here: the text form is a faithful
            // reconstruction of an existing module, and silently re-sorting
            // would hide a non-canonical table from `validate_module`, which
            // is the component whose job it is to reject one.
            return Ok((id, crate::pred::Universe::Members(items)));
        }
        let lo = self.read_i128()?;
        self.expect_str("..=")?;
        let hi = self.read_i128()?;
        Ok((id, crate::pred::Universe::IntRange { lo, hi }))
    }

    /// Parse a predicate table entry: `pred pred.N = <pred>`, mirroring
    /// `Display for Pred`.
    fn parse_pred_def(&mut self) -> Result<(u32, crate::pred::Pred), ParseError> {
        use crate::pred::{Pred, Space};
        self.expect_str("pred")?;
        self.expect_str("pred.")?;
        let id = self.read_u32()?;
        self.expect_char('=')?;
        self.skip_whitespace();
        let rem = self.remaining();
        let pred = if rem.starts_with("in[") {
            self.advance(3)?;
            let lo = self.read_i128()?;
            self.expect_char(',')?;
            let hi = self.read_i128()?;
            self.expect_char(']')?;
            Pred::Interval { lo, hi }
        } else if rem.starts_with("in{") {
            self.advance(3)?;
            self.skip_whitespace();
            let mut items = Vec::new();
            if !self.try_str("}") {
                items.push(self.parse_constant()?);
                while self.try_str(",") {
                    items.push(self.parse_constant()?);
                }
                self.expect_str("}")?;
            }
            Pred::FiniteSet(items)
        } else if rem.starts_with("in_universe(") {
            self.advance(12)?;
            self.expect_str("univ.")?;
            let u = self.read_u32()?;
            self.expect_char(',')?;
            let space = self.read_ident()?;
            let space = match space.as_str() {
                "index" => Space::Index,
                "member" => Space::Member,
                other => return Err(self.error(format!("unknown predicate space: '{other}'"))),
            };
            self.expect_char(')')?;
            Pred::InUniverse(crate::value::UnivId::new(u), space)
        } else if rem.starts_with("and(") || rem.starts_with("or(") {
            let conj = rem.starts_with("and(");
            self.advance(if conj { 4 } else { 3 })?;
            let mut children = Vec::new();
            self.skip_whitespace();
            if !self.try_str(")") {
                loop {
                    self.expect_str("pred.")?;
                    children.push(crate::value::PredId::new(self.read_u32()?));
                    if !self.try_str(",") {
                        break;
                    }
                }
                self.expect_char(')')?;
            }
            if conj {
                Pred::Conj(children)
            } else {
                Pred::Disj(children)
            }
        } else {
            match self.read_ident()?.as_str() {
                "nonzero" => Pred::NonZero,
                "nonnull" => Pred::NonNull,
                "top" => Pred::Top,
                "bottom" => Pred::Bottom,
                other => return Err(self.error(format!("unknown predicate: '{other}'"))),
            }
        };
        Ok((id, pred))
    }

    fn parse_type_def<X: ParseExt>(&mut self) -> Result<(u32, TyG<X>), ParseError> {
        self.expect_str("type")?;
        self.expect_str("ty.")?;
        let id = self.read_u32()?;
        self.expect_char('=')?;
        let ty = self.parse_ty()?;
        Ok((id, ty))
    }

    /// Parse a function type definition: functy.N = (PARAMS...) -> (RETURNS...)
    fn parse_func_ty_def<X: ParseExt>(&mut self) -> Result<(FuncTyId, FuncTyG<X>), ParseError> {
        self.expect_str("functy.")?;
        let id = FuncTyId::new(self.read_u32()?);
        self.expect_char('=')?;
        let (params, is_vararg) = self.parse_func_ty_params()?;
        self.expect_str("->")?;
        let returns = self.parse_ty_list()?;
        let abi = if self.try_str("abi(") {
            let text = self.read_quoted_string()?;
            self.expect_char(')')?;
            Some(
                crate::signature_abi::SignatureAbi::from_canonical_text(&text)
                    .map_err(|e| self.error(e.to_string()))?,
            )
        } else {
            None
        };
        Ok((
            id,
            FuncTyG {
                params,
                returns,
                abi,
                is_vararg,
            },
        ))
    }

    /// Parse a global variable:
    /// global [linkage] [tls(model)] [mut] [align(N)] [visibility(kind)]
    ///        [section("name")] [retained] @Name TY [= VALUE]
    fn parse_global<X: ParseExt>(&mut self) -> Result<GlobalG<X>, ParseError> {
        self.expect_str("global")?;
        let linkage = self.try_parse_linkage()?;
        let tls = self.try_parse_tls_model()?;
        let mutable = self.try_str("mut");
        let align = self.try_parse_global_align()?;
        let visibility = if self.try_str("visibility(") {
            let token = self.read_ident()?;
            let visibility = match token.as_str() {
                "default" => crate::Visibility::Default,
                "hidden" => crate::Visibility::Hidden,
                "protected" => crate::Visibility::Protected,
                other => {
                    return Err(self.error(format!(
                        "unknown global visibility '{other}' (expected default, hidden, protected)"
                    )));
                }
            };
            self.expect_char(')')?;
            visibility
        } else {
            crate::Visibility::Default
        };
        let section = if self.try_str("section(") {
            let section = self.read_quoted_string()?;
            self.expect_char(')')?;
            Some(section)
        } else {
            None
        };
        let retained = self.consume_keyword("retained");
        self.expect_char('@')?;
        let name = self.read_symbol()?;
        let ty = self.parse_ty()?;
        let initializer = if self.try_str("=") {
            Some(self.parse_constant()?)
        } else {
            None
        };
        Ok(GlobalG {
            name,
            ty,
            mutable,
            initializer,
            linkage,
            tls,
            align,
            section,
            visibility,
            retained,
        })
    }

    /// Try to parse a global alignment clause: `align(<N>)`. Returns
    /// `None` when the clause is absent.
    fn try_parse_global_align(&mut self) -> Result<Option<u32>, ParseError> {
        self.skip_whitespace();
        if !self.remaining().starts_with("align(") {
            return Ok(None);
        }
        self.expect_str("align(")?;
        let align = self.read_u32()?;
        self.expect_char(')')?;
        Ok(Some(align))
    }

    /// Parse an ObligationKind from its display name.
    fn parse_obligation_kind(&mut self) -> Result<ObligationKind, ParseError> {
        let name = self.read_ident()?;
        match name.as_str() {
            "precondition" => Ok(ObligationKind::Precondition),
            "postcondition" => Ok(ObligationKind::Postcondition),
            "loop_invariant" => Ok(ObligationKind::LoopInvariant),
            "type_invariant" => Ok(ObligationKind::TypeInvariant),
            "refinement_type" => Ok(ObligationKind::RefinementType),
            "translation_validation" => Ok(ObligationKind::TranslationValidation),
            "memory_safety" => Ok(ObligationKind::MemorySafety),
            "panic_freedom" => Ok(ObligationKind::PanicFreedom),
            "temporal_safety" => Ok(ObligationKind::TemporalSafety),
            "liveness" => Ok(ObligationKind::Liveness),
            "arithmetic_safety" => Ok(ObligationKind::ArithmeticSafety),
            "bounds_check" => Ok(ObligationKind::BoundsCheck),
            "give_back_refinement" => Ok(ObligationKind::GiveBackRefinement),
            // WS4.4 (F-071): the v41 kinds. `custom` is the module-text
            // spelling `custom("<ns>", "<name>")`; the diagnostic `Display`
            // form `custom:<ns>/<name>` is NOT accepted (the `:` ends the
            // identifier), so the kind has one spelling. Namespace ADMISSION
            // is the validator's (`UnpinnedCustomObligationNamespace`), never
            // the parser's.
            "termination" => Ok(ObligationKind::Termination),
            "ownership" => Ok(ObligationKind::Ownership),
            "custom" => {
                self.expect_char('(')?;
                let namespace = self.read_quoted_string()?;
                self.expect_char(',')?;
                let name = self.read_quoted_string()?;
                self.expect_char(')')?;
                Ok(ObligationKind::Custom { namespace, name })
            }
            other => Err(self.error(format!("unknown obligation kind: '{}'", other))),
        }
    }

    /// WS4.4: consume the optional keyword `kw` only when it follows on the
    /// SAME line (and is a whole word). The proof-surface clauses the printer
    /// appends always sit on the line of the item they extend; matching them
    /// across a newline could swallow the start of the next statement.
    fn same_line_keyword(&mut self, kw: &str) -> bool {
        let (saved_pos, saved_line, saved_col) = (self.pos, self.line, self.col);
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with(kw) {
            let boundary = self.remaining()[kw.len()..]
                .chars()
                .next()
                .is_none_or(|ch| ch.is_ascii_whitespace() || matches!(ch, '"' | '[' | '(' | '{'));
            if boundary {
                self.bump_matched(kw);
                return true;
            }
        }
        self.pos = saved_pos;
        self.line = saved_line;
        self.col = saved_col;
        false
    }

    /// `"<alg>"` -> the digest algorithm it names.
    fn parse_digest_algorithm(&mut self) -> Result<ProofDigestAlgorithm, ParseError> {
        match self.read_quoted_string()?.as_str() {
            "sha256" => Ok(ProofDigestAlgorithm::Sha256),
            "trust_ir-stable-v1" => Ok(ProofDigestAlgorithm::TrustIrStableV1),
            other => Err(self.error(format!("unknown proof digest algorithm: '{other}'"))),
        }
    }

    /// `"<alg>" [b0, .., b31]` — `display::write_proof_digest`.
    fn parse_proof_digest(&mut self) -> Result<ProofDigest, ParseError> {
        let algorithm = self.parse_digest_algorithm()?;
        let bytes = self.parse_hash_array()?;
        Ok(ProofDigest { algorithm, bytes })
    }

    /// `["a", "b"]` — `display::write_string_list`.
    fn parse_string_list(&mut self) -> Result<Vec<String>, ParseError> {
        self.expect_char('[')?;
        let mut items = Vec::new();
        self.skip_whitespace();
        if self.peek_char() == Some(']') {
            self.bump();
            return Ok(items);
        }
        loop {
            items.push(self.read_quoted_string()?);
            self.skip_whitespace();
            match self.peek_char() {
                Some(',') => {
                    self.bump();
                }
                Some(']') => {
                    self.bump();
                    return Ok(items);
                }
                other => {
                    return Err(self.error(format!(
                        "expected ',' or ']' in a string list, got {other:?}"
                    )));
                }
            }
        }
    }

    /// `(<u32>)` — the parenthesised index of a sort width or a clause place.
    fn parse_paren_u32(&mut self) -> Result<u32, ParseError> {
        self.expect_char('(')?;
        let n = self.read_u32()?;
        self.expect_char(')')?;
        Ok(n)
    }

    /// `(<u64>)` — a coverage bound's depth or size.
    fn parse_paren_u64(&mut self) -> Result<u64, ParseError> {
        self.expect_char('(')?;
        let n = self.read_u64()?;
        self.expect_char(')')?;
        Ok(n)
    }

    /// WS4.4: one [`ClauseSort`] (`display::write_clause_sort`). Recursive
    /// descent capped at [`crate::text_loss::MAX_TEXT_CLAUSE_SORT_DEPTH`]:
    /// `depth` is the level of the sort being read (1 for the outermost), so
    /// a sort of nesting depth `d` parses iff `d <= 64` — the same count
    /// `text_loss::clause_sort_depth` reports, so the printer never writes a
    /// sort this refuses without a `#lossy` marker.
    fn parse_clause_sort(&mut self, depth: usize) -> Result<ClauseSort, ParseError> {
        use crate::text_loss::MAX_TEXT_CLAUSE_SORT_DEPTH;
        if depth > MAX_TEXT_CLAUSE_SORT_DEPTH {
            return Err(self.error(format!(
                "clause sort nests deeper than {MAX_TEXT_CLAUSE_SORT_DEPTH} levels"
            )));
        }
        let word = self.read_ident()?;
        match word.as_str() {
            "bool" => Ok(ClauseSort::Bool),
            "int" => Ok(ClauseSort::Int),
            "rm" => Ok(ClauseSort::RoundingMode),
            "bv" => Ok(ClauseSort::BitVec(self.parse_paren_u32()?)),
            "float" => {
                self.expect_char('(')?;
                let eb = self.read_u32()?;
                self.expect_char(',')?;
                let sb = self.read_u32()?;
                self.expect_char(')')?;
                Ok(ClauseSort::Float { eb, sb })
            }
            "array" => {
                self.expect_char('(')?;
                let index = self.parse_clause_sort(depth + 1)?;
                self.expect_char(',')?;
                let element = self.parse_clause_sort(depth + 1)?;
                self.expect_char(')')?;
                Ok(ClauseSort::Array(Box::new(index), Box::new(element)))
            }
            "datatype" => {
                self.expect_char('(')?;
                let name = self.read_quoted_string()?;
                self.expect_char(',')?;
                self.expect_char('[')?;
                let mut constructors = Vec::new();
                self.skip_whitespace();
                if self.peek_char() != Some(']') {
                    loop {
                        self.expect_char('(')?;
                        let ctor = self.read_quoted_string()?;
                        self.expect_char(',')?;
                        self.expect_char('[')?;
                        let mut fields = Vec::new();
                        self.skip_whitespace();
                        if self.peek_char() != Some(']') {
                            loop {
                                self.expect_char('(')?;
                                let field = self.read_quoted_string()?;
                                self.expect_char(',')?;
                                let sort = self.parse_clause_sort(depth + 1)?;
                                self.expect_char(')')?;
                                fields.push((field, sort));
                                if !self.try_str(",") {
                                    break;
                                }
                            }
                        }
                        self.expect_char(']')?;
                        self.expect_char(')')?;
                        constructors.push((ctor, fields));
                        if !self.try_str(",") {
                            break;
                        }
                    }
                }
                self.expect_char(']')?;
                self.expect_char(')')?;
                Ok(ClauseSort::Datatype { name, constructors })
            }
            other => Err(self.error(format!(
                "unknown clause sort '{other}' (expected bool, int, bv(N), array(..), \
                 float(EB, SB), rm or datatype(..))"
            ))),
        }
    }

    /// WS4.4: one [`ClausePlace`] (`display::write_clause_place`). Every place
    /// parses wherever a formula appears; which are LEGAL where is the
    /// validator's to decide.
    fn parse_clause_place(&mut self) -> Result<ClausePlace, ParseError> {
        let word = self.read_ident()?;
        match word.as_str() {
            "param" => Ok(ClausePlace::Param {
                index: self.parse_paren_u32()?,
            }),
            "result" => Ok(ClausePlace::ResultSlot {
                index: self.parse_paren_u32()?,
            }),
            "mut_exit" => Ok(ClausePlace::MutParamExit {
                index: self.parse_paren_u32()?,
            }),
            "world" => Ok(ClausePlace::World),
            "unwind" => Ok(ClausePlace::Unwind),
            "value" => {
                self.expect_char('(')?;
                let value = self.read_value_id()?;
                self.expect_char(')')?;
                Ok(ClausePlace::Value(value))
            }
            "spec_var" => Ok(ClausePlace::SpecVar {
                index: self.parse_paren_u32()?,
            }),
            "spec_var_next" => Ok(ClausePlace::SpecVarNext {
                index: self.parse_paren_u32()?,
            }),
            "world_pre" => Ok(ClausePlace::WorldPre),
            "world_post" => Ok(ClausePlace::WorldPost),
            "pointee_entry" => Ok(ClausePlace::ParamPointeeEntry {
                index: self.parse_paren_u32()?,
            }),
            other => Err(self.error(format!(
                "unknown clause place '{other}' (expected param(N), result(N), mut_exit(N), \
                 world, world_pre, world_post, unwind, value(%N), spec_var(N), \
                 spec_var_next(N) or pointee_entry(N))"
            ))),
        }
    }

    /// v59 (WS1.14): the `#effects` payload (`display::write_effect_summary`)
    /// — every field, in declaration order, each named.
    fn parse_effect_summary(&mut self) -> Result<crate::EffectSummary, ParseError> {
        self.expect_keyword_word("reads")?;
        let reads = self.parse_effect_set()?;
        self.expect_keyword_word("writes")?;
        let writes = self.parse_effect_set()?;
        let allocates = self.parse_named_bool("allocates")?;
        let frees = self.parse_named_bool("frees")?;
        let may_unwind = self.parse_named_bool("may_unwind")?;
        let io = self.parse_named_bool("io")?;
        Ok(crate::EffectSummary {
            reads,
            writes,
            allocates,
            frees,
            may_unwind,
            io,
        })
    }

    /// The identifier `word`, exactly (not a prefix of a longer one).
    fn expect_keyword_word(&mut self, word: &str) -> Result<(), ParseError> {
        let got = self.read_ident()?;
        if got == word {
            Ok(())
        } else {
            Err(self.error(format!("expected `{word}`, got '{got}'")))
        }
    }

    /// `<name> true|false` — a strict bool, as the binary decoder's 0/1 byte.
    fn parse_named_bool(&mut self, name: &str) -> Result<bool, ParseError> {
        self.expect_keyword_word(name)?;
        match self.read_ident()?.as_str() {
            "true" => Ok(true),
            "false" => Ok(false),
            other => Err(self.error(format!(
                "expected `true` or `false` after `{name}`, got '{other}'"
            ))),
        }
    }

    /// v59 (WS1.14): `nothing` | `everything` | `places [<place>, ..]`, a place
    /// being `param(N)` or `global(N)`. A place list that is not the ONE
    /// spelling of its set (empty, out of order, duplicated) is refused here,
    /// exactly as the binary, JSON and MessagePack decoders refuse it
    /// (`docs/SPEC_RATIFICATIONS.md` §3).
    fn parse_effect_set(&mut self) -> Result<crate::EffectSet, ParseError> {
        match self.read_ident()?.as_str() {
            "nothing" => Ok(crate::EffectSet::Nothing),
            "everything" => Ok(crate::EffectSet::Everything),
            "places" => {
                self.expect_char('[')?;
                let mut places = Vec::new();
                self.skip_whitespace();
                if self.peek_char() == Some(']') {
                    self.bump();
                } else {
                    loop {
                        places.push(match self.read_ident()?.as_str() {
                            "param" => crate::EffectPlace::ParamPointee {
                                index: self.parse_paren_u32()?,
                            },
                            "global" => {
                                crate::EffectPlace::Global(GlobalId::new(self.parse_paren_u32()?))
                            }
                            other => {
                                return Err(self.error(format!(
                                    "unknown effect place '{other}' (expected param(N) or \
                                     global(N))"
                                )));
                            }
                        });
                        self.skip_whitespace();
                        match self.peek_char() {
                            Some(',') => {
                                self.bump();
                            }
                            Some(']') => {
                                self.bump();
                                break;
                            }
                            other => {
                                return Err(self.error(format!(
                                    "expected ',' or ']' in an effect place list, got {other:?}"
                                )));
                            }
                        }
                    }
                }
                let set = crate::EffectSet::Places(places);
                if !set.is_canonical() {
                    return Err(self.error(format!(
                        "non-canonical effect place list {set:?}: a place list must be \
                         non-empty and strictly ascending, and the empty set is spelled \
                         `nothing` (one-spelling rule, SPEC_RATIFICATIONS §3)"
                    )));
                }
                Ok(set)
            }
            other => Err(self.error(format!(
                "unknown effect set '{other}' (expected nothing, everything or places [..])"
            ))),
        }
    }

    /// WS4.4 (F-064): the one shared formula spelling, `formula "<schema>"
    /// "<payload>" [smtlib ".."] [sort ".."] [bind "<name>" <sort> <place>]*`
    /// (`display::write_proof_formula`). Reads from the `formula` keyword on.
    /// An absent bind list reads back EMPTY — UNBINDABLE, never a wildcard.
    fn parse_proof_formula(&mut self) -> Result<ProofFormula, ParseError> {
        self.expect_str("formula")?;
        let schema = self.read_quoted_string()?;
        let payload = self.read_quoted_string()?;
        // Every trailing clause is matched on the formula's OWN line (review):
        // `consume_keyword` skips newlines, so a failed `smtlib` probe used to
        // leave the cursor on the next line, where a `sort` / `bind` line that
        // is no part of this formula was then read as one of its clauses.
        let smtlib = if self.same_line_keyword("smtlib") {
            Some(self.read_quoted_string()?)
        } else {
            None
        };
        let sort = if self.same_line_keyword("sort") {
            Some(self.read_quoted_string()?)
        } else {
            None
        };
        let mut bindings = Vec::new();
        while self.same_line_keyword("bind") {
            let name = self.read_quoted_string()?;
            let sort = self.parse_clause_sort(1)?;
            let place = self.parse_clause_place()?;
            bindings.push((name, ClauseBinding { sort, place }));
        }
        Ok(ProofFormula {
            schema,
            payload,
            smtlib,
            sort,
            bindings,
        })
    }

    /// `<import> "<symbol>" (none | obligation <id>)`, after its `extern`
    /// keyword — `display::write_extern_ref`. Both tails are matched on the
    /// SAME line: the next statement may begin `obligation N ..`.
    fn parse_extern_ref_tail(&mut self) -> Result<crate::ExternRef, ParseError> {
        let module = self.read_u32()?;
        let symbol = self.read_quoted_string()?;
        self.skip_whitespace_no_newline();
        let obligation = if self.remaining().starts_with("obligation ") {
            self.advance(11)?;
            Some(ProofId::new(self.read_u32()?))
        } else if self.remaining().starts_with("none") {
            self.advance(4)?;
            None
        } else {
            return Err(self.error("expected 'obligation N' or 'none' after an extern symbol"));
        };
        Ok(crate::ExternRef {
            module: crate::ImportId::new(module),
            symbol,
            obligation,
        })
    }

    /// WS4.4 (F-070): `recheck module ".." anchor ".." theorems [..] axioms
    /// [..] [binding ..]`, after its `recheck` keyword —
    /// `display::write_kernel_recheck`.
    fn parse_kernel_recheck_tail(&mut self) -> Result<CleanCicKernelRecheck, ParseError> {
        self.expect_str("module")?;
        let module = self.read_quoted_string()?;
        self.expect_str("anchor")?;
        let anchor = self.read_quoted_string()?;
        self.expect_str("theorems")?;
        let theorems = self.parse_string_list()?;
        self.expect_str("axioms")?;
        let allowed_axioms = self.parse_string_list()?;
        let binding = if self.same_line_keyword("binding") {
            self.expect_str("env")?;
            let environment_digest = self.parse_proof_digest()?;
            self.expect_str("statement")?;
            let statement_digest = self.parse_proof_digest()?;
            let origin_module = if self.same_line_keyword("origin") {
                Some(self.parse_proof_digest()?)
            } else {
                None
            };
            let source = if self.same_line_keyword("source") {
                let decl = self.read_quoted_string()?;
                let closure_digest = self.parse_proof_digest()?;
                Some(SourceDefinitionRef {
                    decl,
                    closure_digest,
                })
            } else {
                None
            };
            self.expect_str("callees")?;
            let callees = self.parse_string_list()?;
            // WS1.13's island, on the same line: the opaque declaration bytes
            // and the digest AS WRITTEN (the validator recomputes and
            // compares it; the reader never repairs one).
            let environment = if self.same_line_keyword("island") {
                let declarations = self.parse_byte_array()?;
                let digest = self.parse_proof_digest()?;
                Some(crate::proof::IslandEnvironment {
                    declarations,
                    digest,
                })
            } else {
                None
            };
            Some(Box::new(CertificateBinding {
                environment_digest,
                statement_digest,
                origin_module,
                source,
                callees,
                environment,
            }))
        } else {
            None
        };
        Ok(CleanCicKernelRecheck {
            module,
            theorems,
            anchor,
            allowed_axioms,
            binding,
        })
    }

    /// WS4.4 (F-064): `assurance <bound> digest "<alg>" [..]`, after its
    /// `assurance` keyword — `display::write_coverage_assurance`.
    fn parse_coverage_assurance_tail(&mut self) -> Result<CoverageAssurance, ParseError> {
        let word = self.read_ident()?;
        let bound = match word.as_str() {
            "unbounded" => CoverageBound::Unbounded,
            "unwind" => CoverageBound::UnwindBounded {
                depth: self.parse_paren_u64()?,
            },
            "model" => CoverageBound::ModelBounded {
                size: self.parse_paren_u64()?,
            },
            "unrecorded" => CoverageBound::Unrecorded,
            other => {
                return Err(self.error(format!(
                    "unknown coverage bound '{other}' (expected unbounded, unwind(N), model(N) \
                     or unrecorded)"
                )));
            }
        };
        self.expect_str("digest")?;
        let request_digest = self.parse_proof_digest()?;
        Ok(CoverageAssurance {
            bound,
            request_digest,
        })
    }

    /// WS4.4: one v46 [`TemporalForm`] (`display::write_temporal_form`).
    fn parse_temporal_form(&mut self) -> Result<TemporalForm, ParseError> {
        let word = self.read_ident()?;
        match word.as_str() {
            "always" => Ok(TemporalForm::Always(self.parse_proof_formula()?)),
            "eventually" => Ok(TemporalForm::Eventually(self.parse_proof_formula()?)),
            "leads_to" => {
                let from = self.parse_proof_formula()?;
                let to = self.parse_proof_formula()?;
                Ok(TemporalForm::LeadsTo(from, to))
            }
            "weak_fair" | "strong_fair" => {
                let action = self.read_quoted_string()?;
                // The relation is optional (NOT RECORDED when absent) and
                // sits on the same line as its property.
                let relation = {
                    let (pos, line, col) = (self.pos, self.line, self.col);
                    if self.same_line_keyword("formula") {
                        self.pos = pos;
                        self.line = line;
                        self.col = col;
                        Some(self.parse_proof_formula()?)
                    } else {
                        None
                    }
                };
                Ok(if word == "weak_fair" {
                    TemporalForm::WeakFair { action, relation }
                } else {
                    TemporalForm::StrongFair { action, relation }
                })
            }
            other => Err(self.error(format!(
                "unknown temporal form '{other}' (expected always, eventually, leads_to, \
                 weak_fair or strong_fair)"
            ))),
        }
    }

    /// Parse a ProofStatus from its display name.
    fn parse_proof_status(&mut self) -> Result<ProofStatus, ParseError> {
        let name = self.read_ident()?;
        match name.as_str() {
            "pending" => Ok(ProofStatus::Pending),
            "discharged" => Ok(ProofStatus::Discharged),
            "failed" => Ok(ProofStatus::Failed),
            "trusted" => Ok(ProofStatus::Trusted),
            "certified" => Ok(ProofStatus::Certified),
            other => Err(self.error(format!("unknown proof status: '{}'", other))),
        }
    }

    /// Parse a proof obligation:
    /// obligation ID KIND STATUS "description"
    /// obligation ID KIND STATUS "description" formula "schema" "payload" [smtlib "..."] [sort "..."]
    fn parse_obligation(&mut self) -> Result<ProofObligation, ParseError> {
        self.expect_str("obligation")?;
        let id = self.read_u32()?;
        let kind = self.parse_obligation_kind()?;
        let status = self.parse_proof_status()?;
        let description = self.read_quoted_string()?;
        // Optional scope clause (B4): `function <id>` precedes any formula.
        let function = if self.consume_keyword("function") {
            Some(FuncId::new(self.read_u32()?))
        } else {
            None
        };
        // WS4.4: the shared formula spelling, clause bindings included.
        let formula = {
            let (pos, line, col) = (self.pos, self.line, self.col);
            if self.consume_keyword("formula") {
                self.pos = pos;
                self.line = line;
                self.col = col;
                Some(self.parse_proof_formula()?)
            } else {
                None
            }
        };
        let source = if self.consume_keyword("source") {
            let source_id = self.read_quoted_string()?;
            self.expect_str("assertion")?;
            let assertion_id = self.read_quoted_string()?;
            let range = if self.consume_keyword("range") {
                Some(ProofObligationSourceRange {
                    file: self.read_u32()?,
                    start_line: self.read_u32()?,
                    start_col: self.read_u32()?,
                    end_line: self.read_u32()?,
                    end_col: self.read_u32()?,
                })
            } else {
                None
            };
            let public = if self.consume_keyword("public") {
                let obligation_id = self.read_quoted_string()?;
                self.expect_str("digest")?;
                Some(PublicObligationIdentity {
                    obligation_id,
                    semantic_digest: self.parse_proof_digest()?,
                })
            } else {
                None
            };
            Some(ProofObligationSourceIdentity {
                source_id,
                assertion_id,
                range,
                public,
            })
        } else {
            None
        };
        // v34 site backref: `site f{F}/bb{B}#{I}`.
        let site = if self.consume_keyword("site") {
            self.expect_char('f')?;
            let site_function = self.read_u32()?;
            self.expect_char('/')?;
            self.expect_str("bb")?;
            let site_block = self.read_u32()?;
            self.expect_char('#')?;
            let inst_index = self.read_u32()?;
            Some(crate::proof::ObligationSite::new(
                FuncId::new(site_function),
                BlockId::new(site_block),
                inst_index,
            ))
        } else {
            None
        };
        // v46 temporal backref: `spec "<machine>" "<temporal>"`. Absent
        // reads as NOT RECORDED, never as a wildcard.
        let spec = if self.consume_keyword("spec") {
            let machine = self.read_quoted_string()?;
            let temporal = self.read_quoted_string()?;
            Some(crate::proof::SpecObligationRef { machine, temporal })
        } else {
            None
        };
        Ok(ProofObligation {
            id: ProofId::new(id),
            kind,
            status,
            description,
            formula,
            function,
            source,
            site,
            spec,
        })
    }

    /// Read a u8 integer.
    fn read_u8(&mut self) -> Result<u8, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(self.error("expected u8 integer"));
        }
        let s = &self.input[start..self.pos];
        s.parse::<u8>()
            .map_err(|_| self.error(format!("invalid u8: '{}'", s)))
    }

    /// Parse a byte array: [N, N, N, ...]
    fn parse_byte_array(&mut self) -> Result<Vec<u8>, ParseError> {
        self.expect_char('[')?;
        let mut bytes = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with(']') {
            bytes.push(self.read_u8()?);
            while self.try_str(",") {
                self.skip_whitespace();
                if self.remaining().starts_with(']') {
                    break;
                }
                bytes.push(self.read_u8()?);
            }
        }
        self.expect_char(']')?;
        Ok(bytes)
    }

    /// Parse a fixed-length 32-byte hash array: [N, N, ..., N] (exactly 32 elements)
    fn parse_hash_array(&mut self) -> Result<[u8; 32], ParseError> {
        let bytes = self.parse_byte_array()?;
        if bytes.len() != 32 {
            return Err(self.error(format!("expected 32-byte hash, got {} bytes", bytes.len())));
        }
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&bytes);
        Ok(hash)
    }

    /// Parse proof evidence: trusted "reason" | kani "name" | lean "term" | smt [bytes] |
    ///   gamma_crown EPSILON LAYERS | translation_validation "rule" [hash]
    fn parse_proof_evidence(&mut self) -> Result<ProofEvidence, ParseError> {
        let kind = self.read_ident()?;
        match kind.as_str() {
            "trusted" => {
                let reason = self.read_quoted_string()?;
                Ok(ProofEvidence::Trusted(reason))
            }
            "kani" => {
                let name = self.read_quoted_string()?;
                Ok(ProofEvidence::KaniHarness(name))
            }
            "lean" => {
                let term = self.read_quoted_string()?;
                Ok(ProofEvidence::LeanProof(term))
            }
            "smt" => {
                let bytes = self.parse_byte_array()?;
                Ok(ProofEvidence::SmtProof(bytes))
            }
            "gamma_crown" => {
                let epsilon = self.read_f64()?;
                let verified_layers = self.read_u32()?;
                Ok(ProofEvidence::GammaCrownBound {
                    epsilon,
                    verified_layers,
                })
            }
            "translation_validation" => {
                let rule_name = self.read_quoted_string()?;
                let smt_hash = self.parse_hash_array()?;
                Ok(ProofEvidence::TranslationValidation {
                    rule_name,
                    smt_hash,
                })
            }
            "inherited" => {
                let callee = self.read_u32()?;
                let obligation = self.read_u32()?;
                // v41 cross-crate clause. Matched WITHOUT crossing a newline:
                // `try_str`/`consume_keyword` skip newlines, and the very next
                // module statement can legitimately begin `external ` — of
                // which "extern" is a prefix. Display always emits this clause
                // on the same line, so a same-line match is exact.
                self.skip_whitespace_no_newline();
                let external = if self.remaining().starts_with("extern ") {
                    self.advance(7)?;
                    // Same-line again, and for the same reason: the module's
                    // own `obligation N ...` statements start the next line.
                    Some(self.parse_extern_ref_tail()?)
                } else {
                    None
                };
                Ok(ProofEvidence::InheritedFromCallee {
                    callee: FuncId::new(callee),
                    obligation: ProofId::new(obligation),
                    external,
                })
            }
            "clean_cic" => {
                let term = self.parse_byte_array()?;
                let context = self.parse_byte_array()?;
                let lineage = self.parse_proof_digest()?;
                // WS4.4 (F-070): the kernel re-check directive, on the same
                // line; absent reads as `None`, exactly the historical text.
                let kernel_recheck = if self.same_line_keyword("recheck") {
                    Some(self.parse_kernel_recheck_tail()?)
                } else {
                    None
                };
                Ok(ProofEvidence::CleanCic {
                    term,
                    context,
                    lineage,
                    kernel_recheck,
                })
            }
            other => Err(self.error(format!("unknown proof evidence kind: '{}'", other))),
        }
    }

    /// Parse a proof certificate: certificate OBLIGATION_ID "prover" EVIDENCE
    fn parse_certificate(&mut self) -> Result<ProofCertificate, ParseError> {
        self.expect_str("certificate")?;
        let obligation_id = self.read_u32()?;
        let prover = self.read_quoted_string()?;
        let evidence = self.parse_proof_evidence()?;
        // WS4.4 (F-064): the v41 coverage projection, on the same line.
        let assurance = if self.same_line_keyword("assurance") {
            Some(self.parse_coverage_assurance_tail()?)
        } else {
            None
        };
        Ok(ProofCertificate {
            obligation: ProofId::new(obligation_id),
            prover,
            evidence,
            assurance,
        })
    }

    /// Parse `diagnostic <id> <severity> "<message>" [at <f> <l> <c>] [detail "<d>"]`.
    fn parse_obligation_diagnostic(&mut self) -> Result<ObligationDiagnostic, ParseError> {
        self.expect_str("diagnostic")?;
        let obligation = ProofId::new(self.read_u32()?);
        self.skip_whitespace_no_newline();
        let sev = self.read_ident()?;
        let severity = match sev.as_str() {
            "error" => DiagnosticSeverity::Error,
            "warning" => DiagnosticSeverity::Warning,
            "note" => DiagnosticSeverity::Note,
            other => return Err(self.error(format!("unknown diagnostic severity: '{other}'"))),
        };
        let message = self.read_quoted_string()?;
        let mut location = None;
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("at ") {
            self.advance(3)?;
            let file = self.read_u32()?;
            self.skip_whitespace_no_newline();
            let line = self.read_u32()?;
            self.skip_whitespace_no_newline();
            let col = self.read_u32()?;
            location = Some(SourceSpan { file, line, col });
        }
        let mut detail = None;
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("detail ") {
            self.advance(7)?;
            detail = Some(self.read_quoted_string()?);
        }
        Ok(ObligationDiagnostic {
            obligation,
            severity,
            message,
            location,
            detail,
        })
    }

    /// Parse a spec_module block. Mirrors `display.rs::write_spec_module`:
    ///
    /// ```text
    /// spec_module "name" {
    ///   origin embedded | origin external "path"
    ///   enforcement design-only | enforcement linked
    ///   var "name" : "ty"
    ///   action "Name"
    ///   invariant "name" : "formula"
    ///   anchor machine "m" action "a" [function <id>] rust "sym" span "s"
    ///          [project "p"]
    ///          [target none | target function <id> |
    ///           target temporal-field-paths-v1 | target external-unresolved]
    ///   waiver machine "m" action "a" reason "why"
    ///   proof machine "m" action "a" name "harness" kind "kani"
    /// }
    /// ```
    fn parse_spec_module(&mut self) -> Result<SpecModule, ParseError> {
        self.expect_str("spec_module")?;
        let name = self.read_quoted_string()?;
        self.expect_char('{')?;

        let mut sm = SpecModule::new(name);
        let mut saw_origin = false;
        let mut saw_enforcement = false;

        loop {
            self.skip_whitespace();
            if self.remaining().starts_with('}') {
                self.bump();
                break;
            }
            if self.is_eof() {
                return Err(self.error("unterminated spec_module block"));
            }

            if self.consume_keyword("origin") {
                if saw_origin {
                    return Err(self.error("spec_module has duplicate `origin` lines"));
                }
                let kind = self.read_ident()?;
                let origin = match kind.as_str() {
                    "embedded" => SpecOrigin::Embedded,
                    "external" => SpecOrigin::External(self.read_quoted_string()?),
                    other => {
                        return Err(self.error(format!("unknown spec origin: '{other}'")));
                    }
                };
                sm.origin = origin;
                saw_origin = true;
            } else if self.consume_keyword("enforcement") {
                if saw_enforcement {
                    return Err(self.error("spec_module has duplicate `enforcement` lines"));
                }
                sm.enforcement = if self.consume_keyword("design-only") {
                    crate::spec::SpecEnforcementMode::DesignOnly
                } else if self.consume_keyword("linked") {
                    crate::spec::SpecEnforcementMode::Linked
                } else {
                    return Err(self.error("unknown spec enforcement mode"));
                };
                saw_enforcement = true;
            } else if self.consume_keyword("var") {
                let vname = self.read_quoted_string()?;
                self.expect_char(':')?;
                let vty = self.read_quoted_string()?;
                // WS4.4: the v46 declared sort, on the same line; absent is
                // `None` (NOT RECORDED).
                let sort = if self.same_line_keyword("sort") {
                    Some(self.parse_clause_sort(1)?)
                } else {
                    None
                };
                sm.vars.push(SpecVar {
                    name: vname,
                    ty: vty,
                    sort,
                });
            } else if self.consume_keyword("action") {
                sm.actions.push(self.read_quoted_string()?);
            } else if self.consume_keyword("invariant") {
                let iname = self.read_quoted_string()?;
                self.expect_char(':')?;
                let formula = self.read_quoted_string()?;
                // WS4.4: the v46 typed first-order carrier, on the same line.
                let typed = if self.same_line_keyword("typed") {
                    Some(self.parse_proof_formula()?)
                } else {
                    None
                };
                sm.invariants.push(SpecInvariant {
                    name: iname,
                    formula,
                    typed,
                });
            } else if self.consume_keyword("temporal") {
                // WS4.4: a v46 named temporal property, in declaration order.
                let name = self.read_quoted_string()?;
                let form = self.parse_temporal_form()?;
                sm.temporal.push(SpecTemporal { name, form });
            } else if self.consume_keyword("anchor") {
                self.expect_str("machine")?;
                let machine = self.read_quoted_string()?;
                self.expect_str("action")?;
                let action = self.read_quoted_string()?;
                let function = if self.consume_keyword("function") {
                    Some(FuncId::new(self.read_u32()?))
                } else {
                    None
                };
                self.expect_str("rust")?;
                let rust_symbol = self.read_quoted_string()?;
                self.expect_str("span")?;
                let span = self.read_quoted_string()?;
                let project = if self.consume_keyword("project") {
                    Some(self.read_quoted_string()?)
                } else {
                    None
                };
                let projection_target = if self.consume_keyword("target") {
                    if self.consume_keyword("none") {
                        None
                    } else if self.consume_keyword("function") {
                        Some(crate::spec::SpecProjectionTarget::Function(FuncId::new(
                            self.read_u32()?,
                        )))
                    } else if self.consume_keyword("temporal-field-paths-v1") {
                        Some(crate::spec::SpecProjectionTarget::TemporalFieldPathsV1)
                    } else if self.consume_keyword("external-unresolved") {
                        Some(crate::spec::SpecProjectionTarget::ExternalUnresolved)
                    } else {
                        return Err(self.error("unknown spec projection target"));
                    }
                } else {
                    crate::spec::SpecProjectionTarget::legacy_compatibility()
                };
                sm.anchors.push(SpecAnchor {
                    machine,
                    action,
                    function,
                    rust_symbol,
                    span,
                    project,
                    projection_target,
                });
            } else if self.consume_keyword("waiver") {
                self.expect_str("machine")?;
                let machine = self.read_quoted_string()?;
                self.expect_str("action")?;
                let action = self.read_quoted_string()?;
                self.expect_str("reason")?;
                let reason = self.read_quoted_string()?;
                sm.waivers.push(SpecWaiver {
                    machine,
                    action,
                    reason,
                });
            } else if self.consume_keyword("proof") {
                self.expect_str("machine")?;
                let machine = self.read_quoted_string()?;
                self.expect_str("action")?;
                let action = self.read_quoted_string()?;
                self.expect_str("name")?;
                let proof_name = self.read_quoted_string()?;
                self.expect_str("kind")?;
                let kind_str = self.read_quoted_string()?;
                let kind = match kind_str.as_str() {
                    "kani" => ProofKind::Kani,
                    // v46: `kind "clean-theorem" theorem "<name>"`.
                    "clean-theorem" => {
                        self.expect_str("theorem")?;
                        ProofKind::CleanTheorem {
                            name: self.read_quoted_string()?,
                        }
                    }
                    other => {
                        return Err(self.error(format!("unknown proof kind: '{other}'")));
                    }
                };
                sm.proofs.push(SpecProof {
                    machine,
                    action,
                    proof_name,
                    kind,
                });
            } else {
                let got: String = self.remaining().chars().take(20).collect();
                return Err(self.error(format!("unexpected token in spec_module: '{got}'")));
            }
        }

        if !saw_origin {
            return Err(self.error("spec_module missing `origin` line"));
        }
        if !saw_enforcement {
            // Explicit, conservative compatibility mapping for legacy text.
            // Current writers always emit the line above.
            sm.enforcement = crate::spec::SpecEnforcementMode::legacy_compatibility();
        }
        Ok(sm)
    }
}

/// Parse a complete TrustIr module from text format.
pub fn parse_module(input: &str) -> Result<Module, ParseError> {
    let mut p = Parser::new(input);
    parse_module_body::<NoExt>(&mut p)
}

/// Parse the text of a level-S template (amendment S): the `template`
/// header, its `param` and `hole` lines, then the module text at
/// `X = TemplateRef`. The structural rules (T1–T5, T7–T9) are checked on the
/// result, so a parsed template is one the binary writer accepts.
pub fn parse_template(input: &str) -> Result<crate::template::Template, ParseError> {
    use crate::template::{
        HoleDef, HoleKind, HostKey, Template, TemplateArg, TemplateHeader, TemplateParam,
        TypeContract,
    };
    let mut p = Parser::new(input);
    p.skip_whitespace();
    while p.remaining().starts_with(';') {
        p.skip_module_comment()?;
        p.skip_whitespace();
    }
    p.expect_str("template")?;
    let identity = p.read_quoted_string()?;
    let mut params = Vec::new();
    loop {
        p.skip_whitespace();
        if !p.remaining().starts_with("param ") {
            break;
        }
        p.advance(6)?;
        p.skip_whitespace();
        p.expect_char('$')?;
        let index = p.read_u32()?;
        if index as usize != params.len() {
            return Err(p.error(format!(
                "template parameter ${index} out of order (expected ${})",
                params.len()
            )));
        }
        p.skip_whitespace();
        let word = p.read_ident()?;
        params.push(match word.as_str() {
            "type" => TemplateParam::Type,
            "const" => TemplateParam::Const {
                ty: p.parse_ty::<NoExt>()?,
            },
            "host" => TemplateParam::Host,
            other => return Err(p.error(format!("unknown template parameter kind '{other}'"))),
        });
    }
    let mut holes = Vec::new();
    loop {
        p.skip_whitespace();
        if !p.remaining().starts_with("hole ") {
            break;
        }
        p.advance(5)?;
        p.skip_whitespace();
        p.expect_char('?')?;
        let index = p.read_u32()?;
        if index as usize != holes.len() {
            return Err(p.error(format!(
                "template hole ?{index} out of order (expected ?{})",
                holes.len()
            )));
        }
        p.skip_whitespace();
        let word = p.read_ident()?;
        let kind = match word.as_str() {
            "type" => {
                p.skip_whitespace();
                let contract = p.read_ident()?;
                HoleKind::Type {
                    contract: match contract.as_str() {
                        "opaque" => TypeContract::Opaque,
                        "struct" => {
                            p.skip_whitespace();
                            p.expect_char('{')?;
                            let mut fields = Vec::new();
                            p.skip_whitespace();
                            if !p.try_str("}") {
                                fields.push(p.parse_ty::<TemplateRef>()?);
                                while p.try_str(",") {
                                    fields.push(p.parse_ty::<TemplateRef>()?);
                                }
                                p.skip_whitespace();
                                p.expect_char('}')?;
                            }
                            TypeContract::Struct { fields }
                        }
                        "enum" => {
                            p.skip_whitespace();
                            p.expect_char('{')?;
                            let mut variants = Vec::new();
                            p.skip_whitespace();
                            if !p.try_str("}") {
                                loop {
                                    p.skip_whitespace();
                                    p.expect_char('[')?;
                                    let mut fields = Vec::new();
                                    p.skip_whitespace();
                                    if !p.try_str("]") {
                                        fields.push(p.parse_ty::<TemplateRef>()?);
                                        while p.try_str(",") {
                                            fields.push(p.parse_ty::<TemplateRef>()?);
                                        }
                                        p.skip_whitespace();
                                        p.expect_char(']')?;
                                    }
                                    variants.push(fields);
                                    if !p.try_str(",") {
                                        break;
                                    }
                                }
                                p.skip_whitespace();
                                p.expect_char('}')?;
                            }
                            p.skip_whitespace();
                            p.expect_str("discriminants")?;
                            p.skip_whitespace();
                            p.expect_char('[')?;
                            let mut discriminants = Vec::new();
                            p.skip_whitespace();
                            if !p.try_str("]") {
                                loop {
                                    p.skip_whitespace();
                                    if p.try_str("none") {
                                        discriminants.push(None);
                                    } else {
                                        discriminants.push(Some(p.read_i128()?));
                                    }
                                    if !p.try_str(",") {
                                        break;
                                    }
                                }
                                p.skip_whitespace();
                                p.expect_char(']')?;
                            }
                            p.skip_whitespace();
                            p.expect_str("repr")?;
                            p.skip_whitespace();
                            let repr = if p.try_str("none") {
                                None
                            } else {
                                Some(p.read_enum_tag_repr()?)
                            };
                            TypeContract::Enum {
                                variants,
                                discriminants,
                                repr,
                            }
                        }
                        other => {
                            return Err(p.error(format!("unknown type contract '{other}'")));
                        }
                    },
                }
            }
            "const" => HoleKind::Const {
                ty: p.parse_ty::<NoExt>()?,
            },
            "callee" => {
                p.skip_whitespace();
                p.expect_str("@func.")?;
                HoleKind::Callee {
                    decl: FuncId::new(p.read_u32()?),
                }
            }
            "global" => {
                p.skip_whitespace();
                p.expect_str("@global.")?;
                HoleKind::Global {
                    decl: GlobalId::new(p.read_u32()?),
                }
            }
            other => return Err(p.error(format!("unknown hole kind '{other}'"))),
        };
        p.skip_whitespace();
        p.expect_str("key")?;
        let namespace = p.read_quoted_string()?;
        p.skip_whitespace();
        let bytes = p.parse_byte_array()?;
        p.skip_whitespace();
        p.expect_str("args")?;
        p.skip_whitespace();
        p.expect_char('(')?;
        let mut args = Vec::new();
        p.skip_whitespace();
        if !p.try_str(")") {
            loop {
                p.skip_whitespace();
                let arg = if p.remaining().starts_with("const ") {
                    p.advance(6)?;
                    let ty = p.parse_ty::<NoExt>()?;
                    let value = p.parse_constant::<TemplateRef>()?;
                    TemplateArg::Const { value, ty }
                } else if p.remaining().starts_with("host ") {
                    p.advance(5)?;
                    p.skip_whitespace();
                    p.expect_char('$')?;
                    TemplateArg::Host(crate::value::ParamId::new(p.read_u32()?))
                } else {
                    TemplateArg::Type(p.parse_ty::<TemplateRef>()?)
                };
                args.push(arg);
                if !p.try_str(",") {
                    break;
                }
            }
            p.skip_whitespace();
            p.expect_char(')')?;
        }
        holes.push(HoleDef {
            kind,
            key: HostKey { namespace, bytes },
            args,
        });
    }
    let module = parse_module_body::<TemplateRef>(&mut p)?;
    let template = Template {
        header: TemplateHeader {
            identity,
            params,
            holes,
        },
        module,
    };
    template
        .check_structure()
        .map_err(|error| p.error(error.to_string()))?;
    Ok(template)
}

/// The module text after a parser's position, at either level: a module file
/// (`X = NoExt`) and a template file's module part (`X = TemplateRef`,
/// amendment S) share the grammar.
fn parse_module_body<X: ParseExt>(p: &mut Parser<'_>) -> Result<ModuleG<X>, ParseError> {
    // Skip header comments (the version header plus any further `;` lines
    // a producer emits before the `module` line).
    // Roadmap WS4.2: a `; #lossy:` marker (printed right after the header
    // when the module had fields text cannot carry) or any other directive
    // here is REFUSED; only plain comments are skipped.
    p.skip_whitespace();
    while p.remaining().starts_with(';') {
        p.skip_module_comment()?;
        p.skip_whitespace();
    }

    // Amendment S: a template is not a module; its text opens with
    // `template`, and only `parse_template` reads it.
    if p.remaining().starts_with("template ") {
        return Err(
            p.error("a template is not a module (amendment S): read it with parse_template")
        );
    }

    // module "name"
    p.expect_str("module")?;
    let name = p.read_quoted_string()?;
    let mut module = ModuleG::<X>::new(name);

    // Optional: target "triple" pointer_size endianness
    //           [abi="<id>"] [structpass=<policy>]
    p.skip_whitespace();
    if p.remaining().starts_with("target ") {
        p.advance(7)?; // "target "
        let triple = p.read_quoted_string()?;
        let pointer_size = p.read_u32()?;
        p.skip_whitespace();
        let endianness_str = p.read_ident()?;
        let endianness = match endianness_str.as_str() {
            "little" => Endianness::Little,
            "big" => Endianness::Big,
            other => return Err(p.error(format!("unknown endianness: '{}'", other))),
        };
        // ABI-pinning trailers (v20). Absent trailers keep the legacy
        // defaults, mirroring the binary codec's pre-v20 read path.
        let mut abi = None;
        let mut struct_passing = crate::StructPassingPolicy::default();
        loop {
            p.skip_whitespace_no_newline();
            if p.remaining().starts_with("abi=") {
                p.advance(4)?;
                abi = Some(p.read_quoted_string()?);
            } else if p.remaining().starts_with("structpass=") {
                p.advance(11)?;
                let policy = p.read_ident()?;
                struct_passing = match policy.as_str() {
                    "native_c" => crate::StructPassingPolicy::NativeC,
                    "always_memory" => crate::StructPassingPolicy::AlwaysMemory,
                    "unclassified" => crate::StructPassingPolicy::Unclassified,
                    other => {
                        return Err(p.error(format!("unknown struct-passing policy: '{}'", other)));
                    }
                };
            } else {
                break;
            }
        }
        module.target_info = Some(TargetInfo {
            triple,
            pointer_size,
            endianness,
            abi,
            struct_passing,
        });
    }

    // Parse struct defs, enum defs, record defs, function type defs, closure tys,
    // globals, functions, obligations, certificates.
    // Functions are numbered in text order by the one fresh-id rule; a text
    // with more functions than `FuncId` can name is refused, never wrapped.
    let mut func_ids = crate::value::FreshIds::<FuncId>::new();

    // Helper: keywords that can start a function definition (linkage or cc prefixes)
    fn is_func_prefix(s: &str) -> bool {
        s.starts_with("fn ")
            || s.starts_with("internal ")
            || s.starts_with("private ")
            || s.starts_with("weak ")
            || s.starts_with("linkonce ")
            // v41 linkages. Missing one here fails LOUDLY since WS4.2: the
            // module loop refuses an unknown top-level line (it used to
            // `skip_line()` and silently DROP the function).
            || s.starts_with("available_externally ")
            || s.starts_with("external_weak ")
            || s.starts_with("weak_odr ")
            || s.starts_with("linkonce_odr ")
            || s.starts_with("external ")
            // Every calling-convention token, derived from `CallingConv::ALL`
            // and its `Display` (WS3.12): a new convention cannot be missed
            // here, which — per the note above — would DROP the function.
            || CallingConv::ALL
                .into_iter()
                .any(|conv| s.starts_with(&format!("{conv} ")))
    }

    loop {
        p.skip_whitespace();
        if p.is_eof() {
            break;
        }
        let rem = p.remaining();

        // Skip plain comment lines; refuse directives (roadmap WS4.2).
        if rem.starts_with(';') {
            p.skip_module_comment()?;
            continue;
        }

        // Debug-info source-file table entries: `file N "path"`, emitted in
        // index order by Display.
        if rem.starts_with("file ") {
            p.advance(5)?;
            let idx = p.read_u32()?;
            let path = p.read_quoted_string()?;
            if idx as usize != module.files.len() {
                return Err(p.error(format!(
                    "source-file table entry {idx} out of order (expected {})",
                    module.files.len()
                )));
            }
            module.files.push(path);
            continue;
        }

        if rem.starts_with("struct ") {
            // The trailing `id=N` is preserved as the StructId (finding E).
            let sd = p.parse_struct_def()?;
            // Nominal text remains ground. Embed its already parsed R fields
            // through the shared exhaustive carrier map for either level.
            module.add_struct(sd.try_map_level(&mut |ty| Ok::<_, ParseError>(ty.embed()))?);
        } else if rem.starts_with("enum ") {
            let ed = p.parse_enum_def()?;
            module.add_enum(ed.try_map_level(&mut |ty| Ok::<_, ParseError>(ty.embed()))?);
        } else if rem.starts_with("record ") {
            let rd = p.parse_record_def()?;
            module.add_record(rd);
        } else if rem.starts_with("import import.") {
            let (id, import) = p.parse_module_import()?;
            let expected = crate::value::table_index(module.imports.len(), "ImportId")
                .map_err(|refusal| p.error(refusal.to_string()))?;
            if id != expected {
                return Err(p.error(format!(
                    "non-contiguous import id: expected import.{expected}, got import.{id}"
                )));
            }
            // Raw push, NOT `intern_import`, for exactly the reason the
            // universe/predicate arms below push raw: parsing RECONSTRUCTS a
            // module text-faithfully, and interning would renumber the table
            // out from under every `ImportId` already embedded in an
            // `ExternRef`. The interning invariant is re-derived by
            // `validate_module`.
            module.imports.push(import);
        } else if rem.starts_with("univ univ.") {
            let (id, universe) = p.parse_universe_def()?;
            let expected = crate::value::table_index(module.universes.len(), "UnivId")
                .map_err(|refusal| p.error(refusal.to_string()))?;
            if id != expected {
                return Err(p.error(format!(
                    "non-contiguous universe id: expected univ.{expected}, got univ.{id}"
                )));
            }
            // Raw push, NOT `intern_universe`: parsing RECONSTRUCTS a module
            // text-faithfully, and interning would renumber the table out from
            // under every `UnivId` already embedded in its predicates. The
            // interning invariant is re-derived by `validate_module`.
            module.universes.push(universe);
        } else if rem.starts_with("pred pred.") {
            let (id, pred) = p.parse_pred_def()?;
            let expected = crate::value::table_index(module.predicates.len(), "PredId")
                .map_err(|refusal| p.error(refusal.to_string()))?;
            if id != expected {
                return Err(p.error(format!(
                    "non-contiguous predicate id: expected pred.{expected}, got pred.{id}"
                )));
            }
            module.predicates.push(pred);
        } else if rem.starts_with("type ty.") {
            // Module `types` table entry (finding A): `type ty.N = <Ty>`.
            let (id, ty) = p.parse_type_def()?;
            let expected = crate::value::table_index(module.types.len(), "TyId")
                .map_err(|refusal| p.error(refusal.to_string()))?;
            if id != expected {
                return Err(p.error(format!(
                    "non-contiguous type id: expected ty.{expected}, got ty.{id}"
                )));
            }
            module
                .add_type(ty)
                .map_err(|refusal| p.error(refusal.to_string()))?;
        } else if rem.starts_with("completeness ") {
            // WS5.3b: the module-level completeness claim. Stated at most
            // once; `partial` is followed by its `unlowered` rows.
            p.expect_str("completeness ")?;
            if module.completeness.is_some() {
                return Err(p.error("duplicate `completeness` claim"));
            }
            if p.try_str("complete") {
                module.completeness = Some(crate::ModuleCompleteness::Complete);
            } else if p.try_str("partial") {
                module.completeness = Some(crate::ModuleCompleteness::Partial(Vec::new()));
            } else {
                return Err(p.error("expected `complete` or `partial` after `completeness`"));
            }
        } else if rem.starts_with("unlowered ") {
            p.expect_str("unlowered")?;
            let symbol = p.read_quoted_string()?;
            p.skip_whitespace();
            let display_path = if p.try_str("-") {
                None
            } else {
                Some(p.read_quoted_string()?)
            };
            let reason = p.read_quoted_string()?;
            match &mut module.completeness {
                Some(crate::ModuleCompleteness::Partial(rows)) => rows.push(crate::UnloweredRow {
                    symbol,
                    display_path,
                    reason,
                }),
                _ => {
                    return Err(p.error(
                        "`unlowered` row outside a `completeness partial` claim — refusing \
                         rather than dropping it",
                    ));
                }
            }
        } else if rem.starts_with("tuple_layout ") {
            p.expect_str("tuple_layout ty.")?;
            let tuple_type = crate::TyId::new(p.read_u32()?);
            p.expect_str("size=")?;
            let size = p.read_u64()?;
            p.expect_str("align=")?;
            let align = p.read_u64()?;
            p.expect_str("offsets=[")?;
            let mut field_offsets = Vec::new();
            if !p.try_str("]") {
                loop {
                    field_offsets.push(p.read_u64()?);
                    if p.try_str("]") {
                        break;
                    }
                    p.expect_char(',')?;
                }
            }
            module.tuple_layouts.push(crate::TupleLayoutDescriptor {
                tuple_type,
                size,
                align,
                field_offsets,
            });
        } else if rem.starts_with("drop_glue ") {
            // Amendment D: "drop_glue @func.N <ty>", one row per line in the
            // table's ONE order (strictly ascending glue, one row per type).
            // Another order is refused, never re-sorted: the text spells
            // exactly one module, as the binary reader does.
            p.expect_str("drop_glue @func.")?;
            let glue = FuncId::new(p.read_u32()?);
            p.skip_whitespace_no_newline();
            let ty = p.parse_ty()?;
            if let Some(previous) = module.drop_glue.last()
                && glue.index() <= previous.glue.index()
            {
                return Err(p.error(format!(
                    "drop_glue @func.{} out of canonical order: rows are strictly ascending by \
                     glue (previous @func.{})",
                    glue.index(),
                    previous.glue.index()
                )));
            }
            if module.drop_glue.iter().any(|entry| entry.ty == ty) {
                return Err(p.error(format!(
                    "drop_glue states a second row for type {ty}: one row per type"
                )));
            }
            module.drop_glue.push(crate::DropGlueEntry { glue, ty });
        } else if rem.starts_with("blob ") {
            // v70: "blob <DIGEST> bytes<HEX>", one row per line in the table's
            // ONE order (strictly ascending digest, so each digest once).
            // Another order is refused, never re-sorted, as the binary reader
            // does. The recorded digest is read as written: whether the bytes
            // hash to it is the validator's question (`InvalidBlobTable`).
            p.expect_str("blob ")?;
            p.skip_whitespace_no_newline();
            let digest = p.read_blob_digest()?;
            p.skip_whitespace_no_newline();
            p.expect_str("bytes<")?;
            let mut data = Vec::new();
            loop {
                p.skip_whitespace();
                if p.try_str(">") {
                    break;
                }
                let hi = p.expect_hex_digit()?;
                let lo = p.expect_hex_digit()?;
                data.push((hi << 4) | lo);
            }
            module.blobs.push(crate::blob::Blob { digest, data });
            if let Some(reason) = crate::blob::blob_table_order_refusal(&module.blobs) {
                return Err(p.error(reason));
            }
        } else if rem.starts_with("closure_layout ") {
            p.expect_str("closure_layout closure.")?;
            let closure = crate::ClosureTyId::new(p.read_u32()?);
            p.expect_str("size=")?;
            let size = p.read_u64()?;
            p.expect_str("align=")?;
            let align = p.read_u64()?;
            p.expect_str("offsets=[")?;
            let mut capture_offsets = Vec::new();
            if !p.try_str("]") {
                loop {
                    capture_offsets.push(p.read_u64()?);
                    if p.try_str("]") {
                        break;
                    }
                    p.expect_char(',')?;
                }
            }
            let origin = p.parse_type_origin_clause()?;
            module.closure_layouts.push(crate::ClosureLayoutDescriptor {
                origin,
                closure,
                size,
                align,
                capture_offsets,
            });
        } else if rem.starts_with("functy.") {
            let (id, ft) = p.parse_func_ty_def()?;
            let expected = crate::value::table_index(module.func_types.len(), "FuncTyId")
                .map_err(|refusal| p.error(refusal.to_string()))?;
            if id.index() != expected {
                return Err(p.error(format!(
                    "non-contiguous function type id: expected functy.{expected}, got functy.{}",
                    id.index()
                )));
            }
            module
                .add_func_type(ft)
                .map_err(|refusal| p.error(refusal.to_string()))?;
        } else if rem.starts_with("closure_ty ") {
            let ct = p.parse_closure_ty_def()?;
            module
                .add_closure_type(ct)
                .map_err(|refusal| p.error(refusal.to_string()))?;
        } else if rem.starts_with("global_asm ") || rem.starts_with("global_asm\t") {
            // WS4.5 (F-065): one module-level `global_asm!` block per line, in
            // source order. Opaque text; the quoted-string reader inverts the
            // printer's escapes exactly.
            p.expect_str("global_asm")?;
            // The block is bound to this LINE: a quote on a following line is
            // not silently adopted.
            p.skip_whitespace_no_newline();
            if !p.remaining().starts_with('"') {
                return Err(p.error("expected a quoted block after `global_asm`"));
            }
            let block = p.read_quoted_string()?;
            module.global_asm.push(block);
        } else if rem.starts_with("global ") || rem.starts_with("global\t") {
            let g = p.parse_global()?;
            module.globals.push(g);
        } else if is_func_prefix(rem) {
            let (mut func, _ft_id) = p.parse_function()?;
            func.id = func_ids
                .take()
                .map_err(|exhausted| p.error(exhausted.to_string()))?;
            // Raw push, NOT `Module::add_function`: parsing RECONSTRUCTS an
            // existing module text-faithfully. `add_function`'s obligation
            // synthesis (roadmap §1.1) must not inject entries the source
            // text does not carry — the `obligation` lines below are the
            // authoritative table and would otherwise duplicate/renumber.
            module.functions.push(func);
        } else if rem.starts_with("obligation ") {
            let po = p.parse_obligation()?;
            module.proof_obligations.push(po);
        } else if rem.starts_with("certificate ") {
            let cert = p.parse_certificate()?;
            module.proof_certificates.push(cert);
        } else if rem.starts_with("diagnostic ") {
            let d = p.parse_obligation_diagnostic()?;
            module.obligation_diagnostics.push(d);
        } else if rem.starts_with("spec_module ") {
            let sm = p.parse_spec_module()?;
            module.spec_modules.push(sm);
        } else {
            // Roadmap WS4.2 (F-065): an unknown top-level line is REFUSED.
            // It used to be skipped, which silently dropped whatever a newer
            // printer (or a missed `is_func_prefix` linkage) wrote there.
            let word: String = rem
                .chars()
                .take_while(|c| !c.is_whitespace())
                .take(48)
                .collect();
            return Err(p.error(format!(
                "unknown directive `{word}` — refusing rather than dropping it"
            )));
        }
    }

    if let Err(error) = X::finish_module(&module) {
        return Err(p.error(error));
    }

    Ok(module)
}

/// Parse a single function from text format.
pub fn parse_function(input: &str) -> Result<Function, ParseError> {
    let mut p = Parser::new(input);
    let (func, _) = p.parse_function()?;
    Ok(func)
}

#[cfg(test)]
#[path = "parser/tensor_gather_scatter_text_tests.rs"]
mod tensor_gather_scatter_text_tests;
#[cfg(test)]
#[path = "parser/tensor_map_reduce_view_text_tests.rs"]
mod tensor_map_reduce_view_text_tests;
#[cfg(test)]
#[path = "parser/tensor_text_tests.rs"]
mod tensor_text_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constant::Constant;
    use crate::inst::{
        BinOp, CastOp, FCmpOp, ICmpOp, Inst, Ordering, OverflowOp, SwitchCase, UnOp,
    };
    use crate::node::InstrNode;
    use crate::ty::{FieldDef, FuncTy, StructDef, Ty};
    use crate::value::{BlockId, FuncId, StructId, ValueId};
    use crate::{Block, Function, Global, Module};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// Every `BinOp` the printer spells is read back by the parser (WS2.21:
    /// the Bool connectives `band`/`bor`/`bxor` were printed but refused as
    /// "unknown instruction"). The match is wildcard-free, so a new `BinOp`
    /// variant fails to compile here until it is listed.
    #[test]
    fn every_binop_display_name_parses_back() {
        fn listed(op: BinOp) -> bool {
            match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::UDiv
                | BinOp::SDiv
                | BinOp::URem
                | BinOp::SRem
                | BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax
                | BinOp::And
                | BinOp::Or
                | BinOp::Xor
                | BinOp::Shl
                | BinOp::LShr
                | BinOp::AShr
                | BinOp::BAnd
                | BinOp::BOr
                | BinOp::BXor
                | BinOp::RotL
                | BinOp::RotR
                | BinOp::FCopySign => true,
            }
        }
        let all = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
            BinOp::FMin,
            BinOp::FMax,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
            BinOp::BAnd,
            BinOp::BOr,
            BinOp::BXor,
            BinOp::RotL,
            BinOp::RotR,
            BinOp::FCopySign,
        ];
        for op in all {
            assert!(listed(op));
            assert_eq!(
                Parser::parse_binop(&op.to_string()),
                Some(op),
                "BinOp::{op:?} prints as `{op}` but does not parse back"
            );
        }
    }

    /// Build a module, display it, parse it, display again, assert identical.
    fn round_trip(module: &Module) {
        let text1 = format!("{}", module);
        let parsed = parse_module(&text1).unwrap_or_else(|e| {
            panic!("parse failed on:\n{}\nerror: {}", text1, e);
        });
        let text2 = format!("{}", parsed);
        assert_eq!(
            text1, text2,
            "Round-trip mismatch.\nOriginal:\n{}\nParsed:\n{}",
            text1, text2
        );
    }

    /// Roadmap WS4.2: a module with fields the text grammar cannot carry
    /// prints a `; #lossy:` marker, and the parser REFUSES it with the named
    /// reason instead of returning a module that silently lacks the fields.
    /// Asserts exactly the loss kinds `expected`, in order.
    fn assert_lossy_refused(module: &Module, expected: &[crate::text_loss::TextLossKind]) {
        let kinds: Vec<_> = crate::text_loss::text_losses(module)
            .iter()
            .map(crate::text_loss::TextLoss::kind)
            .collect();
        assert_eq!(kinds, expected, "text_losses");
        let text = format!("{module}");
        assert!(
            text.lines()
                .nth(1)
                .is_some_and(|l| l.starts_with("; #lossy: ")),
            "the marker must follow the header:\n{text}"
        );
        let err = parse_module(&text).expect_err("a #lossy text must not parse");
        assert!(
            err.message.contains("this text was printed LOSSILY (")
                && err
                    .message
                    .contains("re-emit from the binary/serde artifact"),
            "{err}"
        );
    }

    /// Stronger than [`round_trip`]: assert the PARSED module is structurally
    /// equal to the original (not just that its text is idempotent). This is
    /// what catches silent data loss — a printer that drops a field plus a
    /// parser that defaults it would pass text idempotence but fail this.
    fn round_trip_eq(module: &Module) {
        let text = format!("{}", module);
        let parsed = parse_module(&text).unwrap_or_else(|e| {
            panic!("parse failed on:\n{}\nerror: {}", text, e);
        });
        assert_eq!(
            &parsed, module,
            "structural round-trip lost data.\nText:\n{}",
            text
        );
    }

    /// Build a simple add function: fn add(i64, i64) -> i64 { a + b }
    fn build_add_module() -> Module {
        let mut module = Module::new("test");
        let ft_id = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

        let mut func = Function::new(FuncId::new(0), "add", ft_id, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block.params.push((v(1), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn round_trip_add_module() {
        round_trip(&build_add_module());
    }

    /// v38/v40: both container-tail fat-pointer kinds print and parse back
    /// STRUCTURALLY. `fatptr<container_len>` and `fatptr<container_vtable>`
    /// must not be swallowed by the `str` / `dyn.N` arms, nor by each other.
    #[test]
    fn container_tail_fat_pointers_round_trip_through_text() {
        use crate::ty::FatPtrKind;
        let len = Ty::FatPtr(FatPtrKind::ContainerLen);
        let vtable = Ty::FatPtr(FatPtrKind::ContainerVtable);
        let mut module = Module::new("container_tail");
        let ft_id = module
            .add_func_type(FuncTy {
                params: vec![len.clone(), vtable.clone()],
                returns: vec![vtable.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "pick", ft_id, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), len.clone()));
        block.params.push((v(1), vtable.clone()));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{module}");
        assert!(text.contains("fatptr<container_len>"), "{text}");
        assert!(text.contains("fatptr<container_vtable>"), "{text}");
        round_trip_eq(&module);
    }

    #[test]
    fn unclassified_struct_passing_round_trips_through_canonical_text() {
        let mut module = Module::new("unclassified_target");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-unknown-none".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: crate::StructPassingPolicy::Unclassified,
        });

        let text = format!("{module}");
        assert!(
            text.contains("structpass=unclassified"),
            "the canonical writer must preserve the explicit absence of an ABI classification: {text}"
        );
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_preserves_instruction_source_span() {
        // A node carrying a `SourceSpan` must survive text display -> parse via
        // the `; #loc: <file> <line> <col>` clause. `round_trip_eq` asserts full
        // structural equality, so a dropped or defaulted span fails here (this
        // is the debug-info thread that lets a backtrace resolve file:line).
        use crate::value::SourceSpan;
        let mut module = Module::new("span_test");
        // The debug-info file table the span's `file` index points into.
        module.files.push("src/wholeprog.rs".to_string());
        let ft_id = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "add", ft_id, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block.params.push((v(1), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_span(SourceSpan {
                file: 0,
                line: 42,
                col: 7,
            }),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_ctpop_module() {
        let mut module = Module::new("ctpop_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "pop", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::UnOp {
                op: UnOp::CtPop,
                ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_empty_module() {
        let module = Module::new("empty");
        round_trip(&module);
    }

    #[test]
    fn round_trip_preserves_func_types_table() {
        let mut module = Module::new("func_types");
        let ft0 = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::Ptr],
                returns: vec![Ty::I64, Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .add_func_type(FuncTy {
                params: vec![Ty::Func(ft0), Ty::I8],
                returns: vec![],
                abi: None,
                is_vararg: true,
            })
            .expect("Module::add_func_type: test fixture");

        let text = format!("{}", module);
        assert!(text.contains("functy.0 = (i32, ptr) -> (i64, bool)"));
        assert!(text.contains("functy.1 = (functy.0, i8, ...) -> ()"));

        let parsed = parse_module(&text).unwrap_or_else(|e| {
            panic!("parse failed on:\n{}\nerror: {}", text, e);
        });
        assert_eq!(parsed.func_types, module.func_types);
        assert_eq!(format!("{}", parsed), text);
    }

    #[test]
    fn round_trip_const_and_ret() {
        let mut module = Module::new("consts");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "get42", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_load_store() {
        let mut module = Module::new("mem");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "mem_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_branches() {
        let mut module = Module::new("branches");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "branch", ft, b(0));

        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::Bool));
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        }));
        func.blocks.push(bb0);

        let mut bb1 = Block::new(b(1));
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(1)),
        );
        bb1.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(1)],
        }));
        func.blocks.push(bb1);

        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(2)],
        }));
        func.blocks.push(bb2);

        let mut bb3 = Block::new(b(3));
        bb3.params.push((v(3), Ty::I32));
        bb3.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        func.blocks.push(bb3);

        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_cast() {
        let mut module = Module::new("cast_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "widen", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_f16_float_surface() {
        let mut module = Module::new("f16_surface");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::F16, Ty::F32, Ty::I16],
                returns: vec![Ty::F16],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "half_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::F16));
        block.params.push((v(1), Ty::F32));
        block.params.push((v(2), Ty::I16));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F16,
                value: Constant::Float(0.0),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F16,
                lhs: v(0),
                rhs: v(3),
            })
            .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::FCmp {
                op: FCmpOp::OEq,
                ty: Ty::F16,
                lhs: v(0),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::FPExt,
                src_ty: Ty::F16,
                dst_ty: Ty::F32,
                operand: v(4),
            })
            .with_result(v(6)),
        );
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::FPTrunc,
                src_ty: Ty::F32,
                dst_ty: Ty::F16,
                operand: v(1),
            })
            .with_result(v(7)),
        );
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F16,
                dst_ty: Ty::I16,
                operand: v(4),
            })
            .with_result(v(8)),
        );
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I16,
                dst_ty: Ty::F16,
                operand: v(2),
            })
            .with_result(v(9)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(7)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{}", module);
        assert!(text.contains("f16"));
        assert!(text.contains("fpext f16"));
        assert!(text.contains("fptrunc f32"));
        round_trip(&module);
    }

    #[test]
    fn round_trip_call() {
        let mut module = Module::new("call_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "caller", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_icmp() {
        let mut module = Module::new("icmp_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "cmp", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_coro_suspend() {
        // A 2-state generator's yield point: load state, switch on it, and in
        // the yield arm `coro_suspend %frame, 0, 1, %yielded`.
        let mut module = Module::new("coro");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "gen", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr)); // frame pointer
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(v(1)),
        );
        // coro_suspend %frame(v0), state_slot=0, next_state=1, value=v1
        block.body.push(InstrNode::new(Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(1),
        }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        // Structural-equality round-trip: catches any dropped field.
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_eh_opcodes() {
        // caller() invokes may_throw(); normal -> bb1, unwind -> bb2 (a
        // catch-all landing pad followed by resume). Exercises the text form
        // of all three EH opcodes.
        let mut module = Module::new("eh");
        let callee_ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let caller_ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(Function::new(FuncId::new(0), "may_throw", callee_ft, b(0)))
            .expect("Module::try_add_function: test fixture");

        let mut func = Function::new(FuncId::new(1), "caller", caller_ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        }));
        let mut bb1 = Block::new(b(1));
        bb1.params.push((v(10), Ty::I32));
        bb1.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: false,
                catch_type_indices: vec![0],
            })
            .with_results(vec![v(20), v(21)]),
        );
        bb2.body.push(InstrNode::new(Inst::Resume { exn: v(20) }));
        func.blocks.push(bb0);
        func.blocks.push(bb1);
        func.blocks.push(bb2);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        // Structural-equality round-trip: catches any dropped field.
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_struct_def() {
        let mut module = Module::new("structs");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
            origin: None,
        });
        // WS4.5 FLIPPED THIS: named, offset-bearing fields ARE carried now —
        // `struct @S { name: ty @off }` — so the module is not lossy and the
        // fields survive verbatim. Before WS4.5 this asserted
        // `StructFieldNames` + `StructFieldOffsets` and had to ERASE both
        // before the round trip could be checked.
        assert_eq!(
            crate::text_loss::text_losses(&module),
            vec![],
            "WS4.5: struct field names and offsets are carried"
        );
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_unreachable() {
        let mut module = Module::new("unr");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "panic", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_null_ptr() {
        let mut module = Module::new("null");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "get_null", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::NullPtr).with_result(v(0)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_alloca() {
        let mut module = Module::new("alloca_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_gep() {
        let mut module = Module::new("gep_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_switch() {
        let mut module = Module::new("switch");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::I32],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "sw", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::I32));
        bb0.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(2),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(1),
                target: b(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        }));
        func.blocks.push(bb0);
        let mut bb1 = Block::new(b(1));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(bb1);
        let mut bb2 = Block::new(b(2));
        bb2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(bb2);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    /// WS4.5: the `Switch` exhaustiveness hint survives text EXACTLY, with
    /// a trailing ` exhaustive` and the `#loc` clause after it; an unset flag
    /// prints nothing (and parses back unset).
    #[test]
    fn switch_exhaustive_flag_round_trips_through_text() {
        let mut module = Module::new("switch_exhaustive");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::I32],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module.files.push("a.rs".into());
        let mut func = Function::new(FuncId::new(0), "sw", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::I32));
        bb0.body.push(
            InstrNode::new(Inst::Switch {
                value: v(0),
                default: b(2),
                default_args: vec![],
                cases: vec![SwitchCase {
                    value: Constant::Int(1),
                    target: b(1),
                    args: vec![],
                }],
                exhaustive_enum_unreachable: true,
            })
            .with_span(SourceSpan {
                file: 0,
                line: 1,
                col: 2,
            }),
        );
        func.blocks.push(bb0);
        let mut bb1 = Block::new(b(1));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(bb1);
        let mut bb2 = Block::new(b(2));
        bb2.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(bb2);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        assert!(crate::text_loss::text_losses(&module).is_empty());
        let text = format!("{module}");
        assert!(
            text.contains(" default: bb2 ] exhaustive  ; #loc: 0 1 2"),
            "{text}"
        );
        round_trip_eq(&module);

        // Mutation control: the same text with the keyword deleted is the
        // UNSET flag, and so a different module.
        let unset = parse_module(&text.replacen(" exhaustive", "", 1)).expect("parses");
        assert_ne!(unset, module);
        // The keyword is bound to the instruction: a near-miss is refused.
        refused(&text.replacen(" exhaustive", " exhaustively", 1), "");
    }

    /// WS4.5: `EnumVariant.field_names` round-trips through text when it is
    /// parallel to `fields` (`Name(a: u8, : u16)` — the empty name is `: ty`),
    /// and a variant mixing the two spellings is refused.
    #[test]
    fn enum_variant_field_names_round_trip_through_text() {
        let mut module = Module::new("enum_names");
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "E".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Named".to_string(),
                    fields: vec![Ty::U8, Ty::U16, Ty::Ptr],
                    field_names: vec!["a".into(), String::new(), "needs quoting".into()],
                },
                EnumVariant {
                    name: "Positional".to_string(),
                    fields: vec![Ty::U32],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Unit".to_string(),
                    fields: Vec::new(),
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });
        assert!(crate::text_loss::text_losses(&module).is_empty());
        let text = format!("{module}");
        assert!(
            text.contains(r#"Named(a: u8, : u16, "needs quoting": ptr), Positional(u32), Unit"#),
            "{text}"
        );
        round_trip_eq(&module);

        // Mixing the two spellings in one variant is refused, either way round.
        refused(
            &text.replacen("Named(a: u8, : u16,", "Named(a: u8, u16,", 1),
            "mixes named (`field: ty`) and positional fields",
        );
        refused(
            &text.replacen("Positional(u32)", "Positional(u32, b: u8)", 1),
            "mixes named (`field: ty`) and positional fields",
        );

        // A NON-parallel list (which `validate_module` refuses) cannot be
        // spelled: it is a reported loss and the dump is `#lossy`.
        let mut bad = module.clone();
        bad.enums[0].variants[1].field_names = vec!["x".into(), "y".into()];
        assert_eq!(
            crate::text_loss::text_losses(&bad),
            vec![crate::text_loss::TextLoss::EnumFieldNames {
                enum_id: crate::value::EnumId::new(0)
            }]
        );
        refused(
            &format!("{bad}"),
            "printed LOSSILY (enum-field-names(enum 0))",
        );
    }

    /// WS4.5 (F-065): `Module.global_asm` survives text EXACTLY, block order
    /// and every escape included.
    #[test]
    fn global_asm_blocks_round_trip_through_text() {
        let mut module = build_add_module();
        module.global_asm.push(".globl _x\n_x:\n\tret".into());
        module
            .global_asm
            .push("  .section \"__TEXT\" \\ \u{1} \r\0 é".into());
        assert!(crate::text_loss::text_losses(&module).is_empty());
        let text = format!("{module}");
        assert!(
            text.contains("global_asm \".globl _x\\n_x:\\n\\tret\"\n"),
            "{text}"
        );
        round_trip_eq(&module);
        // The block is bound to its line.
        refused(
            &text.replacen("global_asm \".globl", "global_asm\n\".globl", 1),
            "unknown directive `global_asm`",
        );
    }

    /// WS4.5: review — adversarial spellings of the three new constructs.
    /// Each one is a ParseError; none is read as a different module.
    #[test]
    fn ws45_review_adversarial_spellings_are_refused() {
        // `global_asm`: anything but ONE quoted block on the line is refused.
        let mut asm = build_add_module();
        asm.global_asm.push("nop".into());
        let text = format!("{asm}");
        assert!(text.contains("global_asm \"nop\"\n"), "{text}");
        refused(
            &text.replacen("global_asm \"nop\"", "global_asm nop", 1),
            "expected a quoted block after `global_asm`",
        );
        for bad in [
            "global_asm \"nop\" junk",
            "global_asm \"nop\" \"ret\"",
            "global_asm \"nop",
        ] {
            assert!(
                parse_module(&text.replacen("global_asm \"nop\"", bad, 1)).is_err(),
                "accepted `{bad}`"
            );
        }

        // `switch .. ] exhaustive`: one spelling, bound to the switch's line.
        let mut module = Module::new("sw");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "sw", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::I32));
        bb0.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(1),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(1),
                target: b(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: true,
        }));
        func.blocks.push(bb0);
        let mut bb1 = Block::new(b(1));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(bb1);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        let text = format!("{module}");
        assert!(text.contains("default: bb1 ] exhaustive\n"), "{text}");
        round_trip_eq(&module);
        refused(
            &text.replacen("] exhaustive", "]exhaustive", 1),
            "expected whitespace between `]` and `exhaustive`",
        );
        for bad in [
            "] exhaustive exhaustive",
            "]\n  exhaustive",
            "] Exhaustive",
            "] exhaustive_",
        ] {
            assert!(
                parse_module(&text.replacen("] exhaustive", bad, 1)).is_err(),
                "accepted `{bad}`"
            );
        }
        // Only a `switch` takes the keyword.
        let on_ret = text.replacen("ret\n", "ret exhaustive\n", 1);
        assert_ne!(on_ret, text, "the `ret` edit did not apply");
        assert!(
            parse_module(&on_ret).is_err(),
            "a non-switch instruction accepted `exhaustive`"
        );

        // Enum variant field names: a name the bare grammar cannot carry, a
        // name that is a TYPE keyword, and a `::` path all round-trip; a
        // half-written field is refused.
        let mut module = Module::new("enum_names_adv");
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "E".to_string(),
            variants: vec![EnumVariant {
                name: "V".to_string(),
                fields: vec![Ty::U8, Ty::U16, Ty::Ptr],
                field_names: vec!["u8".into(), "a::b".into(), "line\nbreak \"q\"".into()],
            }],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });
        assert!(crate::text_loss::text_losses(&module).is_empty());
        let text = format!("{module}");
        assert!(text.contains("V(u8: u8, "), "{text}");
        round_trip_eq(&module);
        for (from, to) in [
            ("V(u8: u8,", "V(u8 u8,"),
            ("V(u8: u8,", "V(u8: ,"),
            ("V(u8: u8,", "V(u8:: u8,"),
        ] {
            let edited = text.replacen(from, to, 1);
            assert_ne!(edited, text, "edit `{to}` did not apply");
            assert!(parse_module(&edited).is_err(), "accepted `{to}`\n{edited}");
        }
    }

    #[test]
    fn round_trip_overflow() {
        let mut module = Module::new("overflow");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32, Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "checked_add", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        let node = InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2))
        .with_result(v(3));
        block.body.push(node);
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(2), v(3)],
        }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_multiple_functions() {
        let mut module = Module::new("multi");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for i in 0..3 {
            let mut func = Function::new(FuncId::new(i), format!("func_{i}"), ft, b(0));
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
        }
        round_trip(&module);
    }

    #[test]
    fn round_trip_atomics() {
        let mut module = Module::new("atomics");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "atomic_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering: Ordering::Acquire,
            })
            .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::Release,
        }));
        block.body.push(InstrNode::new(Inst::Fence {
            ordering: Ordering::SeqCst,
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_select() {
        let mut module = Module::new("select");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool, Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "sel", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Bool));
        block.params.push((v(1), Ty::I32));
        block.params.push((v(2), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn parse_comment_lines_between_header_and_module() {
        // Producers may emit extra `;` comment lines between the version
        // header and the `module` line; all of them must be skipped.
        let text = "; trust-ir text format v1\n; produced-by: some-frontend\n; extra note\nmodule \"commented\"\n";
        let parsed = parse_module(text).expect("comment lines before `module` should parse");
        assert_eq!(parsed.name, "commented");
    }

    #[test]
    fn parse_error_has_location() {
        let result = parse_module("garbage input");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.line >= 1);
        assert!(!err.message.is_empty());
    }

    // --- New roundtrip tests for issue #24 ---

    #[test]
    fn round_trip_parameterized_proof_annotations() {
        use crate::proof::ProofAnnotation;
        let mut module = Module::new("param_proofs");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "annotated", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));

        // AtomicOrdering with specific ordering
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1))
            .with_proof(ProofAnnotation::AtomicOrdering(Ordering::Acquire))
            .with_proof(ProofAnnotation::Aligned(16))
            .with_proof(ProofAnnotation::Custom(crate::value::ProofTag::new(42))),
        );

        // BoundedOutput with specific lo/hi
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(5),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::BoundedOutput {
                lo: -1.0,
                hi: 100.0,
            }),
        );

        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_memory_role_and_parallel_annotations() {
        use crate::proof::{Divergence, ProofAnnotation};
        let mut module = Module::new("memory_role_and_parallel");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "scan", ft, b(0));
        func.proofs.push(ProofAnnotation::ReadonlyTable);
        func.proofs.push(ProofAnnotation::AppendOnlyBuffer);
        func.proofs.push(ProofAnnotation::AtomicSetInsert);
        func.proofs.push(ProofAnnotation::ParallelMap);
        func.proofs.push(ProofAnnotation::BoundedLoop(4096));
        func.proofs
            .push(ProofAnnotation::DivergenceClass(Divergence::Uniform));
        func.proofs
            .push(ProofAnnotation::DivergenceClass(Divergence::Low));
        func.proofs
            .push(ProofAnnotation::DivergenceClass(Divergence::High));

        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1))
            .with_proof(ProofAnnotation::ReadonlyTable)
            .with_proof(ProofAnnotation::DivergenceClass(Divergence::Uniform)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    /// REGRESSION (2026-09-21): `discriminants` longer than `variants` used to
    /// round-trip to a DIFFERENT module with an EMPTY loss list — the printer
    /// indexes by variant, so `Some(99)` at index 2 of a two-variant enum was
    /// never printed and no `TextLoss` reported it. The old check only tested
    /// for a trailing `None`, which this shape does not have.
    #[test]
    fn an_overlong_discriminants_vector_is_a_reported_text_loss() {
        use crate::text_loss::{TextLoss, TextLossKind, text_losses};
        use crate::ty::{EnumDef, EnumVariant};
        let mut module = Module::new("disc");
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "E".to_string(),
            variants: vec![
                EnumVariant {
                    name: "A".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "B".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
            // Three entries for two variants, ending in `Some` so the
            // superseded `last().is_some_and(Option::is_none)` test cannot fire.
            discriminants: vec![Some(0), Some(1), Some(99)],
            repr: None,
            layout: None,
            origin: None,
        });

        // It IS a loss, and it is REPORTED — that is the whole fix.
        assert_eq!(
            text_losses(&module)
                .iter()
                .map(TextLoss::kind)
                .collect::<Vec<_>>(),
            vec![TextLossKind::EnumDiscriminantsTail],
        );

        // ANTI-VACUITY: the report has TEETH. Reporting the loss makes
        // `Display` stamp the `; #lossy:` marker, and the parser refuses any
        // text carrying it — so the shape that used to come back silently
        // truncated now does not come back at all. Assert both halves, so a
        // regression that merely stops reporting the loss cannot pass by
        // leaving the text parseable again.
        let text = format!("{module}");
        assert!(
            text.lines()
                .any(|l| l.starts_with("; #lossy: ") && l.contains("enum-discriminants-tail")),
            "{text}"
        );
        let err = parse_module(&text).expect_err("a #lossy text must not parse");
        assert!(err.message.contains("printed LOSSILY"), "{err:?}");

        // And the drop it was hiding was REAL: erase exactly the reported loss
        // (trim the vector to what the text can carry) and the same module
        // round-trips clean. This is the `text_losses` contract in miniature —
        // it also fails if a future change makes the grammar actually CARRY
        // the third entry, which should be rewritten rather than pass here.
        let mut trimmed = module.clone();
        trimmed.enums[0].discriminants.truncate(2);
        assert!(
            text_losses(&trimmed).is_empty(),
            "{:?}",
            text_losses(&trimmed)
        );
        let back = parse_module(&format!("{trimmed}")).expect("parses once trimmed");
        assert_eq!(back.enums[0].discriminants, vec![Some(0), Some(1)]);
    }

    /// The CONTROL for the test above: a discriminants vector that IS the text
    /// reconstruction must report NO loss and round-trip exactly, so the new
    /// check cannot pass by refusing every enum that carries discriminants.
    #[test]
    fn a_well_formed_discriminants_vector_is_not_a_loss() {
        use crate::text_loss::text_losses;
        use crate::ty::{EnumDef, EnumVariant};
        let mut module = Module::new("disc_ok");
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "E".to_string(),
            variants: vec![
                EnumVariant {
                    name: "A".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "B".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
            // Implicit first, explicit last: exactly what printer+parser rebuild.
            discriminants: vec![None, Some(7)],
            repr: None,
            layout: None,
            origin: None,
        });
        assert!(
            text_losses(&module).is_empty(),
            "{:?}",
            text_losses(&module)
        );
        let back = parse_module(&format!("{module}")).expect("parses");
        assert_eq!(back.enums[0].discriminants, module.enums[0].discriminants);
    }

    #[test]
    fn round_trip_enum_def() {
        use crate::ty::{EnumDef, EnumVariant};
        let mut module = Module::new("enums");
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "Option".to_string(),
            variants: vec![
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![Ty::I32],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_enum_complex_variants() {
        use crate::ty::{EnumDef, EnumVariant};
        let mut module = Module::new("complex_enums");
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "Color".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Red".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Green".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Blue".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(1),
            name: "Result".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Ok".to_string(),
                    fields: vec![Ty::I32, Ty::Bool],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Err".to_string(),
                    fields: vec![Ty::I64],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_enum_discriminants_and_repr() {
        use crate::ty::{EnumDef, EnumTagRepr, EnumVariant};
        let mut module = Module::new("sparse_enums");
        // Explicit + implicit discriminant mix (incl. a negative value and an
        // explicit discriminant on a fieldful variant) plus a repr hint:
        // `enum @Sparse repr(i64) { A = -5, B(i64), C = 9223372036854775807 }`.
        module.add_enum(
            EnumDef::new(
                crate::value::EnumId::new(0),
                "Sparse",
                vec![
                    EnumVariant {
                        name: "A".to_string(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "B".to_string(),
                        fields: vec![Ty::I64],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "C".to_string(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(-5), None, Some(i128::from(i64::MAX))])
            .with_repr(EnumTagRepr::I64),
        );
        // An all-implicit enum alongside it keeps the historical text form.
        module.add_enum(EnumDef::new(
            crate::value::EnumId::new(1),
            "Plain",
            vec![EnumVariant {
                name: "Only".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            }],
        ));
        let text = format!("{module}");
        assert!(
            text.contains("enum @Sparse repr(i64) {"),
            "repr hint prints between name and body: {text}"
        );
        assert!(
            text.contains("A = -5"),
            "explicit discriminant prints as `= N`: {text}"
        );
        assert!(
            text.contains("B(i64), C = 9223372036854775807"),
            "implicit variants print bare; fieldful+explicit both print: {text}"
        );
        assert!(
            text.contains("enum @Plain { Only }"),
            "all-implicit enums keep the historical form: {text}"
        );
        round_trip(&module);
    }

    // -----------------------------------------------------------------------
    // WS4.5 (enum half): the `layout(..)` clause
    // -----------------------------------------------------------------------

    /// `enum @Shape repr(u64) { Circle(u64), Rect(u64, u64), Empty }` with the
    /// rustc-derived DIRECT descriptor the two-language battery actually emits
    /// (`size=24 align=8`, tag at 0, payload fields at 8 / 8,16).
    fn direct_layout_enum() -> crate::ty::EnumDef {
        use crate::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
        let variant = |name: &str, fields: Vec<Ty>| EnumVariant {
            name: name.to_string(),
            fields,
            field_names: Vec::new(),
        };
        EnumDef {
            id: crate::value::EnumId::new(0),
            name: "Shape".to_string(),
            variants: vec![
                variant("Circle", vec![Ty::U64]),
                variant("Rect", vec![Ty::U64, Ty::U64]),
                variant("Empty", vec![]),
            ],
            discriminants: Vec::new(),
            repr: Some(EnumTagRepr::U64),
            layout: Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset: 0 },
                size: 24,
                align: 8,
                variant_field_offsets: vec![vec![8], vec![8, 16], vec![]],
            }),
            origin: None,
        }
    }

    /// A module carrying one enum per tag encoding: `Direct`, `Niche` (the
    /// 4-byte `Option<&T>`-shaped image whose `none` is a reserved value of
    /// the payload lane) and v37 `Untagged` (the image IS the sole variant's
    /// payload).
    fn three_encoding_module() -> Module {
        use crate::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
        let variant = |name: &str, fields: Vec<Ty>| EnumVariant {
            name: name.to_string(),
            fields,
            field_names: Vec::new(),
        };
        let mut module = Module::new("enum_layouts");
        module.add_enum(direct_layout_enum());
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(1),
            name: "OptIdx".to_string(),
            variants: vec![variant("some", vec![Ty::U32]), variant("none", vec![])],
            discriminants: Vec::new(),
            repr: None,
            layout: Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Niche {
                    untagged_variant: 0,
                    niche_variants_start: 1,
                    niche_variants_end: 1,
                    niche_start: 0xFFFF_FF01,
                    niche_offset: 0,
                    niche_ty: EnumTagRepr::U32,
                },
                size: 4,
                align: 4,
                variant_field_offsets: vec![vec![0], vec![]],
            }),
            origin: None,
        });
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(2),
            name: "Wrapper".to_string(),
            variants: vec![variant("only", vec![Ty::U64])],
            discriminants: Vec::new(),
            repr: None,
            layout: Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Untagged,
                size: 8,
                align: 8,
                variant_field_offsets: vec![vec![0]],
            }),
            origin: None,
        });
        module
    }

    /// WS4.5 (enum half): all three tag encodings print a `layout(..)` clause
    /// and come back EXACTLY — the descriptor is normative where present, so
    /// anything less than structural equality is a laundered layout.
    #[test]
    fn round_trip_enum_layout_all_three_encodings() {
        let module = three_encoding_module();
        assert_eq!(
            crate::text_loss::text_losses(&module),
            vec![],
            "WS4.5: a well-formed enum layout descriptor is carried"
        );
        let text = format!("{module}");
        assert!(
            text.contains(
                "enum @Shape repr(u64) { Circle(u64), Rect(u64, u64), Empty } \
                 layout(direct tag@0 size=24 align=8 offsets=[[8], [8, 16], []]) id=0"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "layout(niche untagged=0 variants=1..=1 start=4294967041 lane=u32@0 \
                 size=4 align=4 offsets=[[0], []]) id=1"
            ),
            "{text}"
        );
        assert!(
            text.contains("layout(untagged size=8 align=8 offsets=[[0]]) id=2"),
            "{text}"
        );
        round_trip_eq(&module);
    }

    /// NEGATIVE TWIN. Idempotence alone would pass a parser that INVENTED the
    /// descriptor instead of reading it: every enum here is already laid out
    /// the way a canonical recomputation would guess. So edit one number in
    /// the text at a time and require the decoded module to CHANGE — and to
    /// change in exactly that field.
    #[test]
    fn enum_layout_numbers_are_read_from_the_text_not_invented() {
        use crate::ty::EnumTagEncoding;
        let module = three_encoding_module();
        let text = format!("{module}");
        let swapped = text.replace("offsets=[[8], [8, 16], []]", "offsets=[[16], [8, 16], []]");
        assert_ne!(swapped, text);
        let back = parse_module(&swapped).expect("a well-formed variant parses");
        assert_ne!(back, module, "the edited offset must reach the module");
        assert_eq!(
            back.enums[0].layout.as_ref().unwrap().variant_field_offsets[0],
            vec![16]
        );
        // The same for the niche lane's reserved value and the total size.
        let niche = text.replace("start=4294967041", "start=4294967040");
        assert_ne!(niche, text);
        let back = parse_module(&niche).expect("parses");
        assert!(matches!(
            back.enums[1].layout.as_ref().unwrap().encoding,
            EnumTagEncoding::Niche {
                niche_start: 0xFFFF_FF00,
                ..
            }
        ));
        let size = text.replace(
            "layout(untagged size=8 align=8",
            "layout(untagged size=16 align=8",
        );
        assert_ne!(size, text);
        let back = parse_module(&size).expect("parses");
        assert_eq!(back.enums[2].layout.as_ref().unwrap().size, 16);
    }

    /// An internally INCONSISTENT descriptor is the narrowed residual: it is
    /// still a named `EnumLayout` loss, the printer omits the clause, and the
    /// `#lossy` text is refused — never a module carrying a layout its own
    /// enum contradicts. Erasing exactly that field makes it loss-free.
    #[test]
    fn inconsistent_enum_layout_is_refused_not_carried() {
        use crate::text_loss::TextLossKind;
        let mut module = Module::new("bad_layout");
        let mut ed = direct_layout_enum();
        // One offset list too few (two, for three variants): the same shape
        // `Module::enum_layout_shape` fails closed on.
        ed.layout.as_mut().unwrap().variant_field_offsets.pop();
        module.add_enum(ed);
        assert_lossy_refused(&module, &[TextLossKind::EnumLayout]);
        let text = format!("{module}");
        let definition = text
            .lines()
            .find(|line| line.starts_with("enum @"))
            .expect("the enum prints");
        assert!(
            !definition.contains("layout("),
            "an unspellable descriptor must not print a clause at all: {definition}"
        );
        module.enums[0].layout = None;
        round_trip_eq(&module);
    }

    /// REFUSE, NEVER DEFAULT. Each edit below is a layout text a hand editor
    /// (or a newer printer) could write and that the grammar must reject —
    /// accepting any of them would hand a consumer a partially-read
    /// descriptor, which it would then treat as NORMATIVE.
    #[test]
    fn parser_refuses_a_malformed_or_inconsistent_enum_layout() {
        let text = format!("{}", three_encoding_module());
        let cases: &[(&str, &str, &str)] = &[
            // Structural: the offset lists must match the variants exactly.
            (
                "offsets=[[8], [8, 16], []]",
                "offsets=[[8], [8, 16]]",
                "exactly one field-offset list per variant",
            ),
            (
                "offsets=[[8], [8, 16], []]",
                "offsets=[[8], [8], []]",
                "exactly one offset per field",
            ),
            (
                "offsets=[[8], [8, 16], []]",
                "offsets=[[8], [8, 64], []]",
                "field offset lies outside the declared size",
            ),
            // The image: align is a non-zero power of two and divides size.
            (
                "size=24 align=8 offsets=[[8]",
                "size=24 align=3 offsets=[[8]",
                "align must be a non-zero power of two",
            ),
            (
                "size=24 align=8 offsets=[[8]",
                "size=24 align=16 offsets=[[8]",
                "size must be a multiple of its align",
            ),
            // The tag lane: 8 bytes of `repr(u64)` must fit inside the image.
            (
                "direct tag@0",
                "direct tag@20",
                "tag lane lies outside the declared size",
            ),
            // The niche interval must name real variants, be non-empty, and
            // fit its lane.
            ("variants=1..=1", "variants=1..=7", "names no variant"),
            (
                "untagged=0 variants=1..=1",
                "untagged=9 variants=1..=1",
                "names no variant",
            ),
            (
                "variants=1..=1",
                "variants=1..=0",
                "niche interval is empty",
            ),
            (
                "start=4294967041 lane=u32@0",
                "start=4294967296 lane=u32@0",
                "niche value does not fit its lane",
            ),
            (
                "lane=u32@0 size=4",
                "lane=u32@2 size=4",
                "niche lane lies outside the declared size",
            ),
            // v37 `Untagged` describes a tag-FREE image, which is only
            // recoverable when there is exactly one variant.
            // (The second variant comes with its own — correct — empty offset
            // list, so the only thing left to object to is the ENCODING.)
            (
                "enum @Wrapper { only(u64) } layout(untagged size=8 align=8 offsets=[[0]])",
                "enum @Wrapper { only(u64), second } layout(untagged size=8 align=8 offsets=[[0], []])",
                "untagged enum layout requires exactly one variant",
            ),
            // Syntax: an unknown encoding word, a missing key, a missing
            // bracket. None of them may silently yield `layout: None`.
            (
                "layout(untagged size=8",
                "layout(sideways size=8",
                "expected an enum layout encoding",
            ),
            (
                "layout(untagged size=8 align=8",
                "layout(untagged align=8",
                "expected 'size'",
            ),
            (
                "layout(untagged size=8 align=8 offsets=[[0]])",
                "layout(untagged size=8 align=8 offsets=[[0])",
                "expected ']'",
            ),
            (
                "layout(untagged size=8 align=8 offsets=[[0]])",
                "layout(untagged size=8 align=8)",
                "expected 'offsets'",
            ),
        ];
        for (from, to, wanted) in cases {
            let edited = text.replacen(from, to, 1);
            assert_ne!(&edited, &text, "the edit {from:?} -> {to:?} did not apply");
            let err =
                parse_module(&edited).expect_err(&format!("{to:?} must be refused, not defaulted"));
            assert!(
                err.message.contains(wanted),
                "{to:?}: wanted {wanted:?}, got {err}"
            );
        }
        // Control: the unedited text parses and is structurally equal.
        assert_eq!(
            parse_module(&text).expect("control parses"),
            three_encoding_module()
        );
    }

    /// A `layout` word on the LINE BELOW an enum definition is not adopted as
    /// that enum's clause: the trailer is line-bound exactly like `id=N`, so
    /// the id trailer is what must follow the variant list.
    #[test]
    fn enum_layout_clause_is_bound_to_the_definition_line() {
        let text = "; TrustIr text format v1\nmodule \"m\"\n\nenum @E { A }\nlayout(untagged size=0 align=1 offsets=[[]]) id=0\n";
        assert!(parse_module(text).is_err());
    }

    #[test]
    fn round_trip_global_mutable() {
        let mut module = Module::new("globals");
        module.globals.push(crate::Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: crate::Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_global_immutable() {
        let mut module = Module::new("globals");
        module.globals.push(crate::Global {
            name: "PI".to_string(),
            ty: Ty::F64,
            mutable: false,
            initializer: Some(Constant::Float(1.25)),
            linkage: crate::Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_global_no_init() {
        let mut module = Module::new("globals");
        module.globals.push(crate::Global {
            name: "UNINIT".to_string(),
            ty: Ty::I32,
            mutable: false,
            initializer: None,
            linkage: crate::Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let text = format!("{}", module);
        assert!(
            text.contains("\nglobal @UNINIT i32\n"),
            "ordinary global text changed:\n{text}"
        );
        assert!(
            !text.contains("tls("),
            "non-TLS global printed TLS:\n{text}"
        );
        round_trip(&module);
    }

    #[test]
    fn round_trip_global_tls_models() {
        let cases = [
            (crate::TlsModel::LocalExec, "local_exec", "TLS_LOCAL_EXEC"),
            (
                crate::TlsModel::InitialExec,
                "initial_exec",
                "TLS_INITIAL_EXEC",
            ),
            (
                crate::TlsModel::GeneralDynamic,
                "general_dynamic",
                "TLS_GENERAL_DYNAMIC",
            ),
            (
                crate::TlsModel::LocalDynamic,
                "local_dynamic",
                "TLS_LOCAL_DYNAMIC",
            ),
        ];

        for (model, spelling, name) in cases {
            let mut module = Module::new("tls_globals");
            module.globals.push(crate::Global {
                name: name.to_string(),
                ty: Ty::I64,
                mutable: true,
                initializer: Some(Constant::Int(7)),
                linkage: crate::Linkage::Internal,
                tls: Some(model),
                align: None,
                section: None,
                visibility: Default::default(),
                retained: false,
            });

            let text = format!("{}", module);
            let expected = format!("global internal tls({spelling}) mut @{name} i64 = 7");
            assert!(
                text.contains(&expected),
                "TLS global text missing `{expected}`:\n{text}"
            );

            let parsed = parse_module(&text).unwrap_or_else(|e| {
                panic!("parse failed on:\n{}\nerror: {}", text, e);
            });
            assert_eq!(parsed.globals[0].tls, Some(model));
            assert_eq!(format!("{}", parsed), text);
        }
    }

    #[test]
    fn round_trip_proof_obligation() {
        use crate::proof::{ObligationKind, ProofFormula, ProofObligation, ProofStatus};
        let mut module = Module::new("obligations");
        module.proof_obligations.push(ProofObligation {
            id: crate::value::ProofId::new(0),
            kind: ObligationKind::MemorySafety,
            status: ProofStatus::Pending,
            description: "array access in bounds".to_string(),
            formula: Some(ProofFormula::smtlib2("(and (> i 0) (< i len))", "Bool")),
            function: None,
            source: None,
            site: None,
            spec: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: crate::value::ProofId::new(1),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "function is panic-free".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
            spec: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_all_obligation_kinds() {
        use crate::proof::{ObligationKind, ProofObligation, ProofStatus};
        let mut module = Module::new("all_obligations");
        let kinds = [
            ObligationKind::Precondition,
            ObligationKind::Postcondition,
            ObligationKind::LoopInvariant,
            ObligationKind::TypeInvariant,
            ObligationKind::RefinementType,
            ObligationKind::TranslationValidation,
            ObligationKind::MemorySafety,
            ObligationKind::PanicFreedom,
        ];
        for (i, kind) in kinds.into_iter().enumerate() {
            module.proof_obligations.push(ProofObligation {
                id: crate::value::ProofId::new(i as u32),
                kind,
                status: ProofStatus::Pending,
                description: format!("obligation {}", i),
                formula: None,
                function: None,
                source: None,
                site: None,
                spec: None,
            });
        }
        round_trip(&module);
    }

    #[test]
    fn round_trip_proof_certificate_trusted() {
        use crate::proof::{ProofCertificate, ProofEvidence};
        let mut module = Module::new("certificates");
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::Trusted("manual review".to_string()),
            assurance: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_proof_certificate_kani() {
        use crate::proof::{ProofCertificate, ProofEvidence};
        let mut module = Module::new("certificates");
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "kani".to_string(),
            evidence: ProofEvidence::KaniHarness("check_bounds".to_string()),
            assurance: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_proof_certificate_lean() {
        use crate::proof::{ProofCertificate, ProofEvidence};
        let mut module = Module::new("certificates");
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "lean".to_string(),
            evidence: ProofEvidence::LeanProof("theorem foo : True := trivial".to_string()),
            assurance: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_proof_certificate_smt() {
        use crate::proof::{ProofCertificate, ProofEvidence};
        let mut module = Module::new("certificates");
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0xDE, 0xAD, 0xBE, 0xEF]),

            assurance: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_proof_certificate_gamma_crown() {
        use crate::proof::{ProofCertificate, ProofEvidence};
        let mut module = Module::new("certificates");
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "gamma_crown".to_string(),
            evidence: ProofEvidence::GammaCrownBound {
                epsilon: 0.01,
                verified_layers: 5,
            },

            assurance: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_proof_certificate_translation_validation() {
        use crate::proof::{ProofCertificate, ProofEvidence};
        let mut module = Module::new("certificates");
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::TranslationValidation {
                rule_name: "inline".to_string(),
                smt_hash: [0u8; 32],
            },

            assurance: None,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_full_module_with_all_constructs() {
        use crate::proof::{
            ObligationKind, ProofAnnotation, ProofCertificate, ProofEvidence, ProofObligation,
            ProofStatus,
        };
        use crate::ty::{EnumDef, EnumVariant};

        let mut module = Module::new("full");

        // Struct
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
            origin: None,
        });

        // Enum
        module.add_enum(EnumDef {
            id: crate::value::EnumId::new(0),
            name: "Option".to_string(),
            variants: vec![
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![Ty::I32],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });

        // Global
        module.globals.push(crate::Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: crate::Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });

        // Function
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "add", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::NoOverflow),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        // Proof obligation
        module.proof_obligations.push(ProofObligation {
            id: crate::value::ProofId::new(0),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "add is panic-free".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
            spec: None,
        });

        // Proof certificate
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::Trusted("manual review".to_string()),
            assurance: None,
        });

        // WS4.5: struct field names and offsets are carried, so nothing is
        // erased before the round trip.
        assert_eq!(
            crate::text_loss::text_losses(&module),
            vec![],
            "WS4.5: struct field names and offsets are carried"
        );
        round_trip(&module);
    }

    // --- New aggregate / closure types (issue #30) ---

    #[test]
    fn round_trip_set_type_bitset() {
        let mut module = Module::new("set_bitset");
        module
            .add_type(Ty::Set(TyId::new(0), SetRepr::Bitset))
            .expect("Module::add_type: test fixture");
        // A function that uses the type to pin it somewhere in text output
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Set(TyId::new(0), SetRepr::Bitset)],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .params
            .push((v(0), Ty::Set(TyId::new(0), SetRepr::Bitset)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_dialect_op() {
        use crate::dialect::{AttrValue, DialectInst};
        let mut module = Module::new("dialect_mod");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f_dialect", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));

        // A dialect op with two operands, one Ptr result, two attrs (including
        // a Str that round-trips via the quoted form), and a bumped version.
        let op = DialectInst::new("verif", "bfs_step")
            .with_operand(v(0))
            .with_operand(v(1))
            .with_result_ty(Ty::Ptr)
            .with_attr("parallel", AttrValue::Bool(true))
            .with_attr("label", AttrValue::Str("frontier-a".to_string()))
            .with_attr("size", AttrValue::U64(1024))
            .with_attr("delta", AttrValue::I64(-7))
            .with_attr("weight", AttrValue::F64(1.5))
            .with_attr("payload", AttrValue::Bytes(vec![0xde, 0xad, 0xbe, 0xef]))
            .with_attr("elem_ty", AttrValue::Ty(Ty::I32))
            .with_version(3);
        block
            .body
            .push(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(v(2)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        round_trip(&module);
    }

    #[test]
    fn round_trip_set_type_boxed() {
        let mut module = Module::new("set_boxed");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Set(TyId::new(0), SetRepr::Boxed)],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .params
            .push((v(0), Ty::Set(TyId::new(0), SetRepr::Boxed)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_sequence_type() {
        let mut module = Module::new("seq_ty");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Sequence(TyId::new(0))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Sequence(TyId::new(0))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_record_def_and_type() {
        let mut module = Module::new("records");
        module.add_record(crate::ty::RecordDef {
            id: RecordId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
        });
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Record(RecordId::new(0))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "take_rec", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Record(RecordId::new(0))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_closure_def_and_type() {
        let mut module = Module::new("closures");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .add_closure_type(crate::ty::ClosureTy {
                func: ft,
                captures: vec![Ty::I32, Ty::Bool],
            })
            .expect("Module::add_closure_type: test fixture");
        let user_ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Closure(ClosureTyId::new(0))],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "take_clos", user_ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Closure(ClosureTyId::new(0))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn round_trip_sequence_constant_global() {
        let mut module = Module::new("seq_const");
        module.globals.push(Global {
            name: "S".to_string(),
            ty: Ty::Sequence(TyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Sequence(vec![Constant::Int(1), Constant::Int(2)])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_vector_constant_global() {
        let mut module = Module::new("vec_const");
        module.globals.push(Global {
            name: "V".to_string(),
            ty: Ty::Vector(Box::new(Ty::I32), 4),
            mutable: false,
            initializer: Some(Constant::vector_i32([1, -1, 0, 42])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_set_constant_global() {
        let mut module = Module::new("set_const");
        module.globals.push(Global {
            name: "S".to_string(),
            ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            mutable: false,
            initializer: Some(Constant::Set(vec![Constant::Int(7)])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_record_constant_global() {
        let mut module = Module::new("rec_const");
        module.globals.push(Global {
            name: "R".to_string(),
            ty: Ty::Record(RecordId::new(0)),
            mutable: false,
            initializer: Some(Constant::Record(vec![
                ("a".to_string(), Constant::Int(1)),
                ("b".to_string(), Constant::Bool(true)),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_closure_constant_global() {
        let mut module = Module::new("clos_const");
        module.globals.push(Global {
            name: "C".to_string(),
            ty: Ty::Closure(ClosureTyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Closure {
                func: FuncId::new(3),
                captures: vec![Constant::Int(9)],
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_symbol_addr_constant_global() {
        // A mini-vtable global initializer made of relocatable symbol-address
        // elements (function addresses + a data pointer with addend). The text
        // form `symaddr<name>` / `symaddr<name + addend>` must round-trip.
        let mut module = Module::new("symaddr_const");
        module.globals.push(Global {
            name: "VTABLE".to_string(),
            ty: Ty::Tuple(vec![]),
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::symbol_addr("fa"),
                Constant::symbol_addr_with_addend("data_g", 16),
                Constant::symbol_addr_with_addend("neg", -8),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_symbol_addr_dotted_name() {
        // Mangled / path-style symbol names (containing `.`) must round-trip,
        // since `read_ident` accepts `.`.
        let mut module = Module::new("symaddr_dotted");
        module.globals.push(Global {
            name: "P".to_string(),
            ty: Ty::Ptr,
            mutable: false,
            initializer: Some(Constant::symbol_addr("core.fmt.Display")),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_empty_closure_constant() {
        let mut module = Module::new("empty_clos");
        module.globals.push(Global {
            name: "C".to_string(),
            ty: Ty::Closure(ClosureTyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Closure {
                func: FuncId::new(0),
                captures: vec![],
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_dialect_op_no_results_no_attrs() {
        use crate::dialect::DialectInst;
        let mut module = Module::new("dialect_mod2");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "g", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));

        // No results, no attrs, default version -> minimal surface.
        let op = DialectInst::new("verif", "frontier_drain").with_operand(v(0));
        block
            .body
            .push(InstrNode::new(Inst::DialectOp(Box::new(op))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        round_trip(&module);
    }

    // --------- Issues #45 / #46 / #47 regression tests ---------

    /// Build a module with a single global initializer and round-trip it.
    fn wrap_global_and_parse(ty: Ty, c: Constant) -> Constant {
        let mut m = Module::new("t");
        m.globals.push(crate::Global {
            name: "C".to_string(),
            ty,
            mutable: false,
            initializer: Some(c),
            linkage: crate::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let text = format!("{}", m);
        let parsed = parse_module(&text).unwrap_or_else(|e| {
            panic!("parse failed on:\n{}\nerror: {}", text, e);
        });
        parsed.globals[0]
            .initializer
            .as_ref()
            .expect("initializer present")
            .clone()
    }

    /// #45: `Constant::Float(n.0)` must round-trip as a Float, not an Int.
    #[test]
    fn parse_whole_valued_float_roundtrips_as_float() {
        for &v in &[-43075.0_f64, 0.0, -0.0, 1.0, -1.0, 42.0] {
            let got = wrap_global_and_parse(Ty::F64, Constant::Float(v));
            match got {
                Constant::Float(x) => {
                    // Use bit-equality so -0.0 and NaN round-trip
                    // comparisons are exact.
                    assert_eq!(
                        x.to_bits(),
                        v.to_bits(),
                        "float round-trip bits mismatch: in={v} out={x}"
                    );
                }
                other => panic!(
                    "whole-valued float {v} round-tripped as {other:?}, \
                     not Constant::Float (regression of #45)"
                ),
            }
        }
    }

    /// #46: integer literals in the full i128 range must parse.
    #[test]
    fn parse_i128_extremes_roundtrip() {
        for &v in &[
            i128::MAX,
            i128::MIN,
            i128::MIN + 1,
            i128::MAX - 1,
            i64::MAX as i128 + 1,
            (i64::MIN as i128) - 1,
            u64::MAX as i128,
            0i128,
        ] {
            let got = wrap_global_and_parse(Ty::I64, Constant::Int(v));
            assert_eq!(
                got,
                Constant::Int(v),
                "i128 literal {v} did not round-trip (regression of #46)"
            );
        }
    }

    /// #47: finite floats of arbitrary magnitude (including scientific
    /// notation) must parse.
    #[test]
    fn parse_large_magnitude_floats_roundtrip() {
        for &v in &[
            1e300_f64,
            -1e300,
            1e-300,
            -1e-300,
            1.5e38,
            -3.5e38,
            f64::MIN_POSITIVE,
            f64::MAX,
            f64::MIN,
            f64::EPSILON,
        ] {
            let got = wrap_global_and_parse(Ty::F64, Constant::Float(v));
            match got {
                Constant::Float(x) => assert_eq!(
                    x.to_bits(),
                    v.to_bits(),
                    "large-magnitude float round-trip mismatch: in={v} out={x}"
                ),
                other => panic!(
                    "large-magnitude float {v} round-tripped as {other:?} \
                     (regression of #47)"
                ),
            }
        }
    }

    /// Non-finite f64 tokens round-trip through display + parser.
    #[test]
    fn parse_non_finite_floats_roundtrip() {
        // +inf
        let got = wrap_global_and_parse(Ty::F64, Constant::Float(f64::INFINITY));
        match got {
            Constant::Float(x) => assert!(x.is_infinite() && x.is_sign_positive()),
            other => panic!("+inf round-tripped as {other:?}"),
        }
        // -inf
        let got = wrap_global_and_parse(Ty::F64, Constant::Float(f64::NEG_INFINITY));
        match got {
            Constant::Float(x) => assert!(x.is_infinite() && x.is_sign_negative()),
            other => panic!("-inf round-tripped as {other:?}"),
        }
        // NaN (payload is not preserved across text form; equality-by-bits
        // is not required — just the is_nan() classification).
        let got = wrap_global_and_parse(Ty::F64, Constant::Float(f64::NAN));
        match got {
            Constant::Float(x) => assert!(x.is_nan(), "NaN round-tripped to non-NaN {x}"),
            other => panic!("NaN round-tripped as {other:?}"),
        }
    }

    #[test]
    fn parse_fixed_width_vector_type_roundtrip() {
        let text = r#"; TrustIr text format v1
module "vectors"

functy.0 = (<4 x i32>, <4 x i32>) -> (<4 x bool>)

fn @cmp(functy.0) {
bb0(%0: <4 x i32>, %1: <4 x i32>):
    %2 = icmp eq <4 x i32> %0, %1
    ret %2
}
"#;

        let parsed = parse_module(text).expect("parse vector module");
        assert_eq!(
            parsed.func_types[0].params,
            vec![
                Ty::Vector(Box::new(Ty::I32), 4),
                Ty::Vector(Box::new(Ty::I32), 4)
            ]
        );
        assert_eq!(
            parsed.func_types[0].returns,
            vec![Ty::Vector(Box::new(Ty::Bool), 4)]
        );

        let printed = format!("{parsed}");
        assert!(printed.contains("functy.0 = (<4 x i32>, <4 x i32>) -> (<4 x bool>)"));
        assert!(printed.contains("icmp eq <4 x i32> %0, %1"));
    }

    #[test]
    fn parse_vector_select_requires_vector_bool_condition() {
        let text = r#"; TrustIr text format v1
module "vector_select_bad"

functy.0 = (<4 x i32>, <4 x i32>, <4 x i32>) -> (<4 x i32>)

fn @bad_select(functy.0) {
bb0(%0: <4 x i32>, %1: <4 x i32>, %2: <4 x i32>):
    %3 = select <4 x i32> %0, %1, %2
    ret %3
}
"#;

        let err = parse_module(text).expect_err("physical integer mask condition rejected");
        assert!(
            err.message.contains("<4 x bool>"),
            "expected condition type should be reported: {err}"
        );
        assert!(
            err.message.contains("compared to zero"),
            "physical mask conversion should be explicit: {err}"
        );
    }

    #[test]
    fn parse_vector_select_accepts_compare_to_zero_condition() {
        let text = r#"; TrustIr text format v1
module "vector_select_good"

functy.0 = (<4 x i32>, <4 x i32>, <4 x i32>, <4 x i32>) -> (<4 x i32>)

fn @good_select(functy.0) {
bb0(%0: <4 x i32>, %1: <4 x i32>, %2: <4 x i32>, %3: <4 x i32>):
    %4 = icmp ne <4 x i32> %0, %3
    %5 = select <4 x i32> %4, %1, %2
    ret %5
}
"#;

        let parsed = parse_module(text).expect("compare-to-zero mask condition is accepted");
        let printed = format!("{parsed}");
        assert!(printed.contains("icmp ne <4 x i32> %0, %3"));
        assert!(printed.contains("select <4 x i32> %4, %1, %2"));
    }

    #[test]
    fn parse_malformed_vector_types_are_rejected() {
        let parse_vector_param = |ty: &str| {
            parse_module(&format!(
                r#"; TrustIr text format v1
module "bad_vectors"

functy.0 = ({ty}) -> ()
"#
            ))
        };

        let zero_lane = parse_vector_param("<0 x i32>").expect_err("zero lanes are invalid");
        assert!(
            zero_lane
                .message
                .contains("vector lane count must be nonzero"),
            "{zero_lane:?}"
        );

        for (ty, label) in [
            ("<4 i32>", "missing x separator"),
            ("<4 x>", "missing element type"),
            ("<4 x i32", "missing closing bracket"),
            ("<x i32>", "missing lane count"),
        ] {
            assert!(
                parse_vector_param(ty).is_err(),
                "malformed vector type was accepted: {label}"
            );
        }
    }

    // ===================================================================
    // Audit-remediation regressions: text-format round-trip fidelity.
    // ===================================================================

    use crate::proof::{
        ObligationKind, ProofAnnotation, ProofContext, ProofObligation, ProofStatus,
    };
    use crate::ty::{EnumDef, EnumVariant, RecordDef};
    use crate::value::{EnumId, ProofId, RecordId, TyId};

    /// A: the module `types` table must survive a text round trip, including
    /// the `TyId` indices that `Ty::Array`/`Set`/`Sequence` reference.
    #[test]
    fn round_trip_types_table_and_tyid_refs() {
        let mut m = Module::new("types_table");
        let i32_id = m.add_type(Ty::I32).expect("Module::add_type: test fixture"); // ty.0
        let u8_id = m.add_type(Ty::U8).expect("Module::add_type: test fixture"); // ty.1
        let ft = m
            .add_func_type(FuncTy {
                params: vec![
                    Ty::Array(i32_id, 4),
                    Ty::Sequence(u8_id),
                    Ty::Set(i32_id, crate::ty::SetRepr::Bitset),
                ],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "uses_types", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Array(i32_id, 4)));
        block.params.push((v(1), Ty::Sequence(u8_id)));
        block
            .params
            .push((v(2), Ty::Set(i32_id, crate::ty::SetRepr::Bitset)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{}", m);
        assert!(
            text.contains("type ty.0 = i32"),
            "types table missing:\n{text}"
        );
        assert!(text.contains("type ty.1 = u8"));
        round_trip_eq(&m);
    }

    /// B: function-level proofs and FuncAttrs/ParamAttrs must round-trip.
    #[test]
    fn round_trip_function_proofs_and_attrs() {
        let mut m = Module::new("fn_meta");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "annotated", ft, b(0));
        func.proofs.push(ProofAnnotation::Pure);
        func.proofs.push(ProofAnnotation::Wrapping);
        func.attrs.readonly = true;
        func.attrs.inlinehint = true;
        // Both params carry attrs so the positional `params` length is
        // preserved exactly (a TRAILING all-default `ParamAttrs` is treated as
        // absent by the printer — equivalent to `FuncAttrs::is_empty` — so it
        // would not be re-materialized; that is by design, not data loss).
        func.attrs.params = vec![
            crate::ParamAttrs {
                dereferenceable: Some(16),
                nonnull: true,
                align: Some(8),
                noalias: true,
                readonly: true,
                byval: true,
                sret: false,
                ext: crate::ArgExt::None,
                pass: None,
            },
            crate::ParamAttrs {
                noalias: true,
                sret: true,
                ..crate::ParamAttrs::default()
            },
        ];
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I32));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{}", m);
        assert!(text.contains("; #proof: pure, wrapping"), "{text}");
        assert!(text.contains("; #attrs: readonly inlinehint"), "{text}");
        assert!(
            text.contains(
                "; #param_attrs 0: dereferenceable(16) nonnull align(8) noalias readonly byval"
            ),
            "{text}"
        );
        assert!(text.contains("; #param_attrs 1: noalias sret"), "{text}");
        round_trip_eq(&m);
    }

    /// v23: the `; #producer:` header clause must round-trip for every
    /// vocabulary token and for the quoted `Other` escape (including escape
    /// characters), and `Other("trust")` must NOT collapse into `TRust`.
    #[test]
    fn round_trip_function_producer_clause() {
        let producers = [
            Producer::TRust,
            Producer::Clean,
            Producer::TrustIr,
            Producer::TSwift,
            Producer::TC,
            Producer::Other("custom \"quoted\" frontend\n".to_string()),
            // A quoted known token stays Other — provenance is not normalized.
            Producer::Other("trust".to_string()),
        ];
        let mut m = Module::new("producer_meta");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for (i, producer) in producers.iter().enumerate() {
            let mut func = Function::new(FuncId::new(i as u32), format!("f{i}"), ft, b(0));
            func.producer = Some(producer.clone());
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            m.try_add_function(func)
                .expect("Module::try_add_function: test fixture");
        }

        let text = format!("{}", m);
        assert!(text.contains("; #producer: trust\n"), "{text}");
        assert!(text.contains("; #producer: clean\n"), "{text}");
        assert!(text.contains("; #producer: trust-ir\n"), "{text}");
        assert!(text.contains("; #producer: tswift\n"), "{text}");
        assert!(text.contains("; #producer: tc\n"), "{text}");
        assert!(text.contains("; #producer: \"trust\"\n"), "{text}");
        // Structural equality through print→parse covers every producer field
        // (Function's PartialEq includes `producer`).
        round_trip_eq(&m);
    }

    /// v61: the `; #body-gate:` clause carries a license's `GateEvidence`
    /// (`evidence #<obligation> "<digest>"`) and round-trips it; an
    /// evidence-free license keeps its v41 spelling, and a malformed evidence
    /// clause is a parse error, never a silently evidence-free license.
    #[test]
    fn round_trip_body_gate_evidence_clause() {
        let mut m = Module::new("gate_evidence_text");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let digest = crate::proof::ProofDigest::sha256([0xab; 32]);
        for (i, evidence) in [
            None,
            Some(crate::GateEvidence {
                obligation: crate::ProofId::new(7),
                body_digest: digest,
            }),
        ]
        .into_iter()
        .enumerate()
        {
            let mut func = Function::new(FuncId::new(i as u32), format!("f{i}"), ft, b(0));
            func.body_gate = Some(crate::BodyGate::Gated {
                authority: "clean-kernel-tv".to_string(),
                evidence,
            });
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            m.try_add_function(func)
                .expect("Module::try_add_function: test fixture");
        }
        let text = format!("{}", m);
        assert!(
            text.contains("; #body-gate: gated \"clean-kernel-tv\"\n"),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "; #body-gate: gated \"clean-kernel-tv\" evidence #7 \"{digest}\"\n"
            )),
            "{text}"
        );
        round_trip_eq(&m);

        // Every malformed evidence clause is a parse error, never a license
        // with the evidence silently dropped (review: one twin per field).
        let shown = digest.to_string();
        let hex = shown.strip_prefix("sha256:").expect("sha256 display");
        let quoted = format!("\"sha256:{hex}\"");
        let short = format!("\"sha256:{}\"", &hex[1..]);
        let unknown = format!("\"md5:{hex}\"");
        let spaced = format!(" {quoted}");
        for (from, to, what) in [
            ("evidence #7", "evidence 7", "an obligation without its `#`"),
            (
                "evidence #7",
                "evidence #",
                "an obligation without a number",
            ),
            (quoted.as_str(), short.as_str(), "a 63-hex-digit digest"),
            (
                quoted.as_str(),
                unknown.as_str(),
                "an unknown digest algorithm",
            ),
            (spaced.as_str(), "", "no digest at all"),
        ] {
            let broken = text.replace(from, to);
            assert_ne!(broken, text, "the mutation `{what}` applied");
            assert!(
                parse_module(&broken).is_err(),
                "{what} must not parse:\n{broken}"
            );
        }
    }

    #[test]
    fn round_trip_semantic_source_provenance_directives() {
        let mut m = Module::new("source_provenance_text");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::U64],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "looping", ft, b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U64));
        entry.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0)],
        }));
        let mut header = Block::new(b(1));
        header.params.push((v(1), Ty::U64));
        header.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        }));
        func.blocks.extend([entry, header]);
        func.source_provenance = Some(SourceProvenance::new(
            ProofDigest::sha256([0x11; 32]),
            ProofDigest::sha256([0x22; 32]),
            vec![SourceLoopProvenance {
                source_loop_id: 0,
                hir_local_id: 71,
                header: b(1),
                bindings: vec![SourceBindingProvenance {
                    name: "x, quoted \"source\"".into(),
                    hir_local_id: 72,
                    place: SourcePlace::LoopParameter { index: 0 },
                }],
            }],
        ));
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{m}");
        assert!(text.contains("; #source-provenance: schema 1"), "{text}");
        assert!(text.contains("; #source-loop: 0 hir 71 header 1"), "{text}");
        assert!(text.contains("loop-param 0"), "{text}");
        round_trip_eq(&m);
    }

    #[test]
    fn source_binding_without_preceding_loop_is_rejected() {
        let digest = ProofDigest::sha256([1; 32]);
        let text = format!(
            "; TrustIr text format v1\nmodule \"bad_source\"\n\nfuncty.0 = () -> ()\n\nfn @f(functy.0) {{\n    ; #source-provenance: schema 1 compiler \"{digest}\" semantic \"{digest}\" binding \"{digest}\"\n    ; #source-binding: loop 0 name \"x\" hir 1 loop-param 0\nbb0():\n    ret\n}}\n"
        );
        let error = parse_module(&text).expect_err("binding without loop must fail closed");
        assert!(error.message.contains("exactly one preceding #source-loop"));
    }

    /// v32/v33: value names, the lexical-scope tree, and per-node scope
    /// indices are one text-round-trippable debug-information surface.
    #[test]
    fn round_trip_function_names_and_lexical_scopes() {
        let mut m = Module::new("debug_meta");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "named", ft, b(0));
        func.value_names = Some(vec![
            (v(7), "input, \"quoted\"\n".to_string()),
            (v(9), "result".to_string()),
        ]);
        func.scopes = Some(vec![
            ScopeData {
                parent: None,
                span: Some(SourceSpan {
                    file: 0,
                    line: 1,
                    col: 0,
                }),
                inlined_at: None,
            },
            ScopeData {
                parent: Some(0),
                span: None,
                inlined_at: None,
            },
        ]);
        let mut block = Block::new(b(0));
        block.params.push((v(7), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::I32,
                operand: v(7),
            })
            .with_result(v(9))
            .with_scope(1),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(9)] }).with_scope(0));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{m}");
        assert!(
            text.contains("; #names: %7=\"input, \\\"quoted\\\"\\n\", %9=\"result\""),
            "{text}"
        );
        assert!(text.contains("; #scope: 0 root at 0 1 0"), "{text}");
        assert!(text.contains("; #scope: 1 parent=0"), "{text}");
        assert!(text.contains("; #scope: 1"), "{text}");
        round_trip_eq(&m);
    }

    /// C: ProofObligation.function (B4) and InstrNode.proof_context (B5).
    #[test]
    fn round_trip_obligation_function_and_proof_context() {
        let mut m = Module::new("ctx");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "caller", ft, b(0));
        let mut block = Block::new(b(0));
        // A call carrying a per-call-site proof context.
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            })
            .with_proof_context(ProofContext {
                assumes: vec![ProofId::new(1), ProofId::new(2)],
                establishes: vec![ProofId::new(3)],
            }),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Discharged,
                "scoped",
            )
            .with_function(FuncId::new(0)),
        );

        let text = format!("{}", m);
        assert!(
            text.contains("function 0"),
            "obligation scope missing:\n{text}"
        );
        assert!(
            text.contains("#proof_ctx: assumes[1,2] establishes[3]"),
            "proof_context missing:\n{text}"
        );
        round_trip_eq(&m);
    }

    /// C: a proof_context with empty assumes/establishes round-trips too.
    #[test]
    fn round_trip_empty_proof_context() {
        let mut m = Module::new("empty_ctx");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "c", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            })
            .with_proof_context(ProofContext::default()),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip_eq(&m);
    }

    /// D: ValueRange / KnownBits / Wrapping / ProofRef all round-trip through text.
    #[test]
    fn round_trip_value_fact_proof_annotations() {
        let mut m = Module::new("value_facts");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        func.proofs.push(ProofAnnotation::ValueRange {
            lo: i128::MIN,
            hi: i128::MAX,
        });
        func.proofs.push(ProofAnnotation::KnownBits {
            zeros: u128::MAX,
            ones: 0,
        });
        func.proofs.push(ProofAnnotation::Wrapping);
        func.proofs.push(ProofAnnotation::ProofRef(ProofId::new(7)));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip_eq(&m);
    }

    /// The four information-flow / havoc markers `Display` emits but the
    /// parser could not read: `parse(print(m))` hard-failed with "unknown
    /// proof annotation" on any module carrying one, breaking the crate's own
    /// text fixed-point guarantee. The conformance corpus never caught it
    /// because no fixture carries any of the four.
    ///
    /// Not hypothetical: trust-ir-bridge emits `FreshSymbolicHavoc` at 57
    /// sites and `RegionHavocStore` in production, and the producer writes
    /// canonical text out as a shipped `<crate>.trust-ir.txt` artifact — so
    /// today's artifact for any crate with an Undef havoc could not be re-read.
    ///
    /// Both placements are covered: a function-level annotation and an
    /// instruction-level one parse through different call sites.
    ///
    /// The havoc markers sit where the validator admits them since WS2.11
    /// (`HavocMarkerMisplaced`): `FreshSymbolicHavoc` on an `undef` node and
    /// `RegionHavocStore` on a non-volatile `store` node — this test used to
    /// stamp both on the `return`, a placement no producer emits and the
    /// validator now refuses. The parser itself is placement-agnostic (it
    /// reads text, it does not validate), so the round trip is unchanged.
    #[test]
    fn round_trip_infoflow_and_havoc_proof_annotations() {
        let mut m = Module::new("infoflow");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        func.proofs.push(ProofAnnotation::Tainted);
        func.proofs.push(ProofAnnotation::TrustedSink);
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        let mut fresh = InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(1));
        fresh.proofs.push(ProofAnnotation::FreshSymbolicHavoc);
        block.body.push(fresh);
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(2)),
        );
        let mut havoc_store = InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(2),
            value: v(0),
            volatile: false,
            align: None,
        });
        havoc_store.proofs.push(ProofAnnotation::RegionHavocStore);
        block.body.push(havoc_store);
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip_eq(&m);
    }

    /// E: sparse/non-contiguous struct/enum/record ids must be preserved.
    ///
    /// Struct fields use the text format's type-only spelling (`{ ty }`), so
    /// the struct here carries no field names/offsets — those are preserved by
    /// the binary/JSON/MessagePack paths, not the text debug form. The focus of
    /// this test is the sparse id trailers (`id=5`/`id=9`/`id=3`).
    #[test]
    fn round_trip_sparse_struct_enum_record_ids() {
        let mut m = Module::new("sparse_ids");
        m.add_struct(StructDef {
            id: StructId::new(5),
            name: "S".into(),
            fields: vec![FieldDef {
                name: String::new(),
                ty: Ty::I32,
                offset: None,
            }],
            size: Some(8),
            align: Some(4),

            repr: Default::default(),
            origin: None,
        });
        m.add_enum(EnumDef {
            id: EnumId::new(9),
            name: "E".into(),
            variants: vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            }],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
            origin: None,
        });
        m.add_record(RecordDef {
            id: RecordId::new(3),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "x".into(),
                ty: Ty::Bool,
                offset: None,
            }],
        });
        // A function whose signature references the SPARSE ids.
        let ft = m
            .add_func_type(FuncTy {
                params: vec![
                    Ty::Struct(StructId::new(5)),
                    Ty::Enum(EnumId::new(9)),
                    Ty::Record(RecordId::new(3)),
                ],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Struct(StructId::new(5))));
        block.params.push((v(1), Ty::Enum(EnumId::new(9))));
        block.params.push((v(2), Ty::Record(RecordId::new(3))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let text = format!("{}", m);
        assert!(
            text.contains("struct @S { i32 } size=8 align=4 id=5"),
            "{text}"
        );
        assert!(text.contains("enum @E { V(i64) } id=9"), "{text}");
        assert!(text.contains("record @R { x: bool } id=3"), "{text}");
        round_trip_eq(&m);
    }

    /// F: dialect op with non-finite F64 attrs and control-char Str attrs.
    #[test]
    fn round_trip_dialect_nonfinite_and_control_chars() {
        use crate::dialect::{AttrEntry, AttrValue, DialectInst};
        let mut m = Module::new("dialect_edge");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "d", ft, b(0));
        let mut block = Block::new(b(0));
        let mut op = DialectInst::new("edge", "op");
        op.attrs = vec![
            AttrEntry {
                name: "nan".into(),
                value: AttrValue::F64(f64::NAN),
            },
            AttrEntry {
                name: "inf".into(),
                value: AttrValue::F64(f64::INFINITY),
            },
            AttrEntry {
                name: "neg_inf".into(),
                value: AttrValue::F64(f64::NEG_INFINITY),
            },
            AttrEntry {
                name: "finite".into(),
                value: AttrValue::F64(3.5),
            },
            AttrEntry {
                name: "ctrl".into(),
                value: AttrValue::Str("a\r\n\t\0b\u{7}c".into()),
            },
        ];
        block
            .body
            .push(InstrNode::new(Inst::DialectOp(Box::new(op))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        // NaN != NaN, so a structural assert on the module would spuriously
        // fail; instead parse and compare the decoded attrs bit-for-bit.
        let text = format!("{}", m);
        let parsed = parse_module(&text).expect("parse dialect edge text");
        let orig_attrs = match &m.functions[0].blocks[0].body[0].inst {
            Inst::DialectOp(o) => &o.attrs,
            _ => unreachable!(),
        };
        let got_attrs = match &parsed.functions[0].blocks[0].body[0].inst {
            Inst::DialectOp(o) => &o.attrs,
            _ => panic!("parsed first inst is not a dialect op"),
        };
        assert_eq!(orig_attrs.len(), got_attrs.len());
        for (a, bv) in orig_attrs.iter().zip(got_attrs.iter()) {
            assert_eq!(a.name, bv.name);
            match (&a.value, &bv.value) {
                (AttrValue::F64(x), AttrValue::F64(y)) => {
                    assert_eq!(x.to_bits(), y.to_bits(), "f64 attr {} bits drifted", a.name);
                }
                (AttrValue::Str(x), AttrValue::Str(y)) => {
                    assert_eq!(x, y, "str attr {} lost control chars", a.name);
                }
                (x, y) => assert_eq!(x, y),
            }
        }
    }

    /// G (fixed): `Ty::Unit` spells `()` and the zero-element tuple spells
    /// `(,)`, so they are textually distinct and each survives a text round
    /// trip as itself (previously both rendered `()` and `Unit` collapsed to
    /// the empty tuple).
    #[test]
    fn unit_and_empty_tuple_round_trip_distinctly() {
        let round_trip = |param: Ty| {
            let mut m = Module::new("u");
            let ft = m
                .add_func_type(FuncTy {
                    params: vec![param],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            m.try_add_function(Function::new(FuncId::new(0), "f", ft, b(0)))
                .expect("Module::try_add_function: test fixture");
            let text = format!("{}", m);
            parse_module(&text).unwrap().func_types[0].params[0].clone()
        };
        assert_eq!(round_trip(Ty::Unit), Ty::Unit);
        assert_eq!(round_trip(Ty::Tuple(Vec::new())), Ty::Tuple(Vec::new()));
        let _ = TyId::new(0); // keep TyId import used across cfg paths
    }
    // --- WS4.2: the strict parser (F-065) ---

    /// The WS4.2 control text: a lossless module that parses exactly.
    fn strict_base() -> (Module, String) {
        let mut module = build_add_module();
        module.functions[0]
            .proofs
            .push(crate::proof::ProofAnnotation::Pure);
        module.functions[0].blocks[0].body[0].span = Some(SourceSpan {
            file: 0,
            line: 3,
            col: 4,
        });
        module.files.push("a.rs".into());
        let text = format!("{module}");
        assert!(crate::text_loss::text_losses(&module).is_empty());
        assert_eq!(parse_module(&text).expect("control parses"), module);
        (module, text)
    }

    fn refused(text: &str, needle: &str) {
        let err = parse_module(text).expect_err("strict parser must refuse");
        assert!(err.message.contains(needle), "{err}\n{text}");
    }

    /// Mutation control for the strict half: a `; #contract:` line from a
    /// hypothetical newer printer returns `ParseError`, not `Ok` with the
    /// field missing (the pre-WS4.2 behaviour). (`#summary` was this test's
    /// example until WS4.4 gave it a spelling; a line in some OTHER spelling
    /// is still refused, by the summary grammar.)
    #[test]
    fn strict_unknown_function_directive_is_refused() {
        let (_, text) = strict_base();
        let newer = text.replacen(
            "    ; #proof: pure\n",
            "    ; #proof: pure\n    ; #contract: requires \"(> x 0)\"\n",
            1,
        );
        assert_ne!(newer, text);
        refused(
            &newer,
            "unknown directive `#contract` — refusing rather than dropping it",
        );
        let misspelled = text.replacen(
            "    ; #proof: pure\n",
            "    ; #proof: pure\n    ; #summary: requires \"(> x 0)\"\n",
            1,
        );
        refused(
            &misspelled,
            "expected `proved` or `unproved` after #summary, got 'requires'",
        );
    }

    #[test]
    fn strict_unknown_node_directive_is_refused() {
        let (_, text) = strict_base();
        let newer = text.replacen("  ; #loc: 0 3 4", "  ; #loc: 0 3 4  ; #weight: 7", 1);
        assert_ne!(newer, text);
        refused(&newer, "unknown directive `#weight`");
    }

    #[test]
    fn strict_unknown_top_level_line_is_refused() {
        let (_, text) = strict_base();
        // (`global_asm` was this test's example until WS4.5 gave it a
        // spelling; any word a newer printer might write stands in.)
        let newer = format!("{text}\nmodule_asm \".globl _x\"\n");
        refused(
            &newer,
            "unknown directive `module_asm` — refusing rather than dropping it",
        );
        // A misspelled linkage used to DROP the whole function silently.
        let dropped = text.replacen("fn @add", "weakodr fn @add", 1);
        refused(&dropped, "unknown directive `weakodr`");
    }

    #[test]
    fn strict_misplaced_and_module_level_directives_are_refused() {
        let (_, text) = strict_base();
        // `#loc` is a node clause, never a function-header directive.
        let misplaced = text.replacen("    ; #proof: pure\n", "    ; #loc: 0 1 1\n", 1);
        refused(
            &misplaced,
            "directive `#loc` is not valid in a function header",
        );
        // `#names` is a function-header directive, never a node clause.
        let on_node = text.replacen("  ; #loc: 0 3 4", "  ; #names: %0=\"a\"", 1);
        refused(
            &on_node,
            "directive `#names` is not valid on an instruction",
        );
        // No directive is valid between top-level items.
        let top = format!("{text}\n; #producer: trust\n");
        refused(&top, "directive `#producer` is not valid at module level");
    }

    #[test]
    fn strict_lossy_marker_is_refused_anywhere_at_module_level() {
        let (_, text) = strict_base();
        let marked = text.replacen(
            "; TrustIr text format v1\n",
            "; TrustIr text format v1\n; #lossy: global-asm(1 blocks)\n",
            1,
        );
        refused(
            &marked,
            "this text was printed LOSSILY (global-asm(1 blocks)); it cannot be parsed back \
             — re-emit from the binary/serde artifact",
        );
        refused(&format!("{text}; #lossy: x\n"), "printed LOSSILY (x)");
    }

    /// Plain comments (a `;` not followed by `#`) are still skipped at
    /// module level, in the header and after an instruction.
    #[test]
    fn strict_parser_still_skips_plain_comments() {
        let (module, text) = strict_base();
        let commented = text
            .replacen(
                "; TrustIr text format v1\n",
                "; TrustIr text format v1\n; produced by hand\n",
                1,
            )
            .replacen("  ; #loc: 0 3 4", "  ; #loc: 0 3 4  ; the sum", 1)
            + "\n; trailing note: #not-a-directive\n";
        assert_eq!(parse_module(&commented).expect("plain comments"), module);
    }

    // ------------------------------------------------------------------
    // Roadmap WS4.4: text carries the proof surface (F-064, F-070, F-071).
    // ------------------------------------------------------------------

    fn ws44_digest(fill: u8) -> crate::proof::ProofDigest {
        crate::proof::ProofDigest::sha256([fill; 32])
    }

    fn ws44_bound(
        schema: &str,
        payload: &str,
        bindings: Vec<(&str, crate::proof::ClauseSort, crate::proof::ClausePlace)>,
    ) -> crate::proof::ProofFormula {
        let mut formula = crate::proof::ProofFormula::new(schema, payload);
        formula.bindings = bindings
            .into_iter()
            .map(|(name, sort, place)| {
                (
                    name.to_string(),
                    crate::proof::ClauseBinding { sort, place },
                )
            })
            .collect();
        formula
    }

    /// Every `ClauseSort` constructor, nested, including a datatype with
    /// constructors and fields and a by-name (constructor-free) datatype.
    fn ws44_every_sort() -> Vec<crate::proof::ClauseSort> {
        use crate::proof::ClauseSort;
        vec![
            ClauseSort::Bool,
            ClauseSort::Int,
            ClauseSort::BitVec(64),
            ClauseSort::Array(
                Box::new(ClauseSort::BitVec(64)),
                Box::new(ClauseSort::Array(
                    Box::new(ClauseSort::Int),
                    Box::new(ClauseSort::Bool),
                )),
            ),
            ClauseSort::Float { eb: 11, sb: 53 },
            ClauseSort::RoundingMode,
            ClauseSort::Datatype {
                name: "Option<u64> \"q\"".into(),
                constructors: vec![
                    ("None".into(), vec![]),
                    (
                        "Some".into(),
                        vec![
                            ("0".into(), ClauseSort::BitVec(64)),
                            (
                                "nested".into(),
                                ClauseSort::Datatype {
                                    name: "List".into(),
                                    constructors: vec![],
                                },
                            ),
                        ],
                    ),
                ],
            },
            ClauseSort::Datatype {
                name: "ByName".into(),
                constructors: vec![],
            },
        ]
    }

    /// `f(i64, &mut i64) -> i64` with a body defining `%0,%1` (params) and
    /// `%2` (a result), carrying a summary with EVERY clause kind (requires,
    /// ensures, decreases, params, proved) and bindings of every function
    /// `ClausePlace`, plus a body-less `g` whose summary is `backed_by` an
    /// import; obligations of every v41 kind with bindings of every place and
    /// every sort; certificates of every `CoverageBound`; a `clean_cic`
    /// certificate with a recheck directive (bound and unbound).
    fn ws44_proof_surface_module() -> Module {
        use crate::proof::{
            CertificateBinding, ClausePlace, ClauseSort, CleanCicKernelRecheck, CoverageAssurance,
            CoverageBound, ObligationKind, ProofCertificate, ProofEvidence, ProofObligation,
            ProofStatus, SourceDefinitionRef,
        };
        use crate::value::{ImportId, ProofId};
        let mut module = Module::new("ws44");
        let import = module
            .intern_import(
                crate::ModuleImport::new("dep", ws44_digest(0x11)).with_producer(Producer::Clean),
            )
            .expect("Module::intern_import: test fixture");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::I64, Ty::RefMut(Box::new(Ty::I64))],
                returns: vec![Ty::I64],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block.params.push((v(1), Ty::RefMut(Box::new(Ty::I64))));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(0),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(block);
        f.summary = Some(
            FunctionSummary::new()
                .with_params(vec!["a".into(), "b \"quoted\"".into()])
                .requiring(ws44_bound(
                    "smtlib2",
                    "(bvsge a #x0000000000000000)",
                    vec![("a", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 })],
                ))
                .requiring(crate::proof::ProofFormula::smtlib2("true", "Bool"))
                .ensuring(ws44_bound(
                    "trust-types.Formula@1",
                    "{\"op\":\"eq\"}",
                    vec![
                        (
                            "result",
                            ClauseSort::BitVec(64),
                            ClausePlace::ResultSlot { index: 0 },
                        ),
                        (
                            "b'",
                            ClauseSort::BitVec(64),
                            ClausePlace::MutParamExit { index: 1 },
                        ),
                        ("heap", ClauseSort::Int, ClausePlace::World),
                        ("unw", ClauseSort::Bool, ClausePlace::Unwind),
                        ("sum", ClauseSort::BitVec(64), ClausePlace::Value(v(2))),
                    ],
                ))
                .decreasing(ws44_bound(
                    "smtlib2",
                    "a",
                    vec![("a", ClauseSort::Int, ClausePlace::Param { index: 0 })],
                ))
                .proved(),
        );
        module.functions.push(f);
        let g_summary = FunctionSummary::new()
            .with_params(vec!["a".into(), "b".into()])
            .ensuring(crate::proof::ProofFormula::smtlib2("(= 1 1)", "Bool"))
            .proved()
            .backed_by(crate::ExternRef::new(import, "g").relying_on(ProofId::new(7)));
        module
            .functions
            .push(Function::declaration(FuncId::new(1), "g", ft, g_summary));
        // An empty summary is `Some(default)`, not `None`.
        let mut h = Function::declaration(FuncId::new(2), "h", ft, FunctionSummary::new());
        h.summary = Some(FunctionSummary {
            backed_by: Some(crate::ExternRef::new(ImportId::new(0), "h")),
            ..FunctionSummary::default()
        });
        module.functions.push(h);

        let kinds = [
            ObligationKind::Termination,
            ObligationKind::Ownership,
            ObligationKind::Custom {
                namespace: "trust.concurrency".into(),
                name: "no \"race\"".into(),
            },
            ObligationKind::Custom {
                namespace: "".into(),
                name: "x".into(),
            },
            ObligationKind::Postcondition,
            ObligationKind::GiveBackRefinement,
        ];
        for (i, kind) in kinds.into_iter().enumerate() {
            let sorts = ws44_every_sort();
            let places = [
                ClausePlace::Param { index: 0 },
                ClausePlace::ResultSlot { index: 0 },
                ClausePlace::MutParamExit { index: 1 },
                ClausePlace::World,
                ClausePlace::Unwind,
                ClausePlace::Value(v(2)),
                ClausePlace::SpecVar { index: 3 },
                ClausePlace::SpecVarNext { index: 4 },
            ];
            let names: Vec<String> = (0..sorts.len()).map(|k| format!("x{k}")).collect();
            let bindings = sorts
                .into_iter()
                .zip(places.iter().cycle())
                .zip(&names)
                .map(|((sort, place), name)| (name.as_str(), sort, *place))
                .collect();
            let mut formula = ws44_bound("smtlib2", "(and true true)", bindings);
            formula.smtlib = Some("(and true true)".into());
            formula.sort = Some("Bool".into());
            module.proof_obligations.push(
                ProofObligation::new(ProofId::new(i as u32), kind, ProofStatus::Pending, "o")
                    .with_function(FuncId::new(0))
                    .with_formula(formula),
            );
        }
        let bounds = [
            CoverageBound::Unbounded,
            CoverageBound::UnwindBounded { depth: 3 },
            CoverageBound::ModelBounded { size: u64::MAX },
            CoverageBound::Unrecorded,
        ];
        for (i, bound) in bounds.into_iter().enumerate() {
            module.proof_certificates.push(ProofCertificate {
                obligation: ProofId::new(i as u32),
                prover: "p".into(),
                evidence: ProofEvidence::Trusted("audit".into()),
                assurance: Some(CoverageAssurance {
                    bound,
                    request_digest: ws44_digest(i as u8),
                }),
            });
        }
        let recheck = |binding| CleanCicKernelRecheck {
            module: "Crownproof.Slack \"Z\"".into(),
            theorems: vec!["NNVerify.a".into(), "NNVerify.b".into()],
            anchor: "nn_verify_farkas_constructive".into(),
            allowed_axioms: vec![],
            binding,
        };
        let evidence = |kernel_recheck| ProofEvidence::CleanCic {
            term: vec![1, 2, 3],
            context: vec![],
            lineage: ws44_digest(9),
            kernel_recheck,
        };
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(4),
            prover: "clean".into(),
            evidence: evidence(Some(recheck(None))),
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(4),
            prover: "clean".into(),
            evidence: evidence(Some(recheck(Some(Box::new(CertificateBinding::new(
                ws44_digest(1),
                ws44_digest(2),
            )))))),
            assurance: Some(CoverageAssurance {
                bound: CoverageBound::Unbounded,
                request_digest: ws44_digest(3),
            }),
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(5),
            prover: "clean".into(),
            evidence: evidence(Some(recheck(Some(Box::new(CertificateBinding {
                environment_digest: ws44_digest(4),
                statement_digest: ws44_digest(5),
                origin_module: Some(ws44_digest(6)),
                source: Some(SourceDefinitionRef {
                    decl: "Clean.f".into(),
                    closure_digest: ws44_digest(7),
                }),
                callees: vec!["a".into(), "b c".into()],
                // WS1.13's island. The digest deliberately does NOT match the
                // bytes: text carries it AS STORED (the validator recomputes
                // and refuses a mismatch; the reader must never repair one).
                environment: Some(crate::proof::IslandEnvironment {
                    declarations: vec![0, 7, 255],
                    digest: ws44_digest(8),
                }),
            }))))),
            assurance: None,
        });
        module
    }

    /// Positive: the whole proof surface survives `print -> parse` EXACTLY
    /// (structural equality, not text idempotence), with no `#lossy` marker.
    #[test]
    fn ws44_proof_surface_round_trips_exactly() {
        let module = ws44_proof_surface_module();
        assert!(
            crate::text_loss::text_losses(&module).is_empty(),
            "{:?}",
            crate::text_loss::text_losses(&module)
        );
        let text = format!("{module}");
        assert!(!text.contains("#lossy"), "{text}");
        round_trip_eq(&module);
        round_trip(&module);
        // The spellings are the documented ones.
        for needle in [
            "    ; #summary: proved params [\"a\", \"b \\\"quoted\\\"\"]\n",
            "    ; #requires: formula \"smtlib2\" \"(bvsge a #x0000000000000000)\" bind \"a\" bv(64) param(0)\n",
            "bind \"b'\" bv(64) mut_exit(1) bind \"heap\" int world bind \"unw\" bool unwind bind \"sum\" bv(64) value(%2)",
            "    ; #decreases: formula \"smtlib2\" \"a\" bind \"a\" int param(0)\n",
            "    ; #backed-by: extern 0 \"g\" obligation 7\n",
            "    ; #backed-by: extern 0 \"h\" none\n",
            "    ; #summary: unproved params []\n",
            "obligation 0 termination pending",
            "obligation 1 ownership pending",
            "obligation 2 custom(\"trust.concurrency\", \"no \\\"race\\\"\") pending",
            "obligation 3 custom(\"\", \"x\") pending",
            "array(bv(64), array(int, bool))",
            "float(11, 53)",
            " rm ",
            "datatype(\"Option<u64> \\\"q\\\"\", [(\"None\", []), (\"Some\", [(\"0\", bv(64)), (\"nested\", datatype(\"List\", []))])])",
            "spec_var(3)",
            "spec_var_next(4)",
            " assurance unbounded digest \"sha256\" [",
            " assurance unwind(3) digest ",
            " assurance model(18446744073709551615) digest ",
            " assurance unrecorded digest ",
            " recheck module \"Crownproof.Slack \\\"Z\\\"\" anchor \"nn_verify_farkas_constructive\" theorems [\"NNVerify.a\", \"NNVerify.b\"] axioms []",
            " binding env \"sha256\" [",
            " origin \"sha256\" [",
            " source \"Clean.f\" \"sha256\" [",
            " callees [\"a\", \"b c\"] island [0, 7, 255] \"sha256\" [8, 8,",
        ] {
            assert!(text.contains(needle), "missing {needle:?} in:\n{text}");
        }
    }

    /// A binding-free formula, a recheck-less certificate and an
    /// assurance-less certificate keep their EXACT pre-WS4.4 bytes: the new
    /// clauses are printed only when present.
    #[test]
    fn ws44_absent_proof_surface_prints_the_historical_bytes() {
        use crate::proof::{
            ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation,
            ProofStatus,
        };
        use crate::value::ProofId;
        let mut module = Module::new("legacy");
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "d",
            )
            .with_formula(ProofFormula::smtlib2("(= x 1)", "Bool")),
        );
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "clean".into(),
            evidence: ProofEvidence::CleanCic {
                term: vec![1],
                context: vec![2],
                lineage: ws44_digest(0),
                kernel_recheck: None,
            },
            assurance: None,
        });
        let text = format!("{module}");
        let zeros = vec!["0"; 32].join(", ");
        assert!(text.contains(
            "\nobligation 0 postcondition pending \"d\" formula \"smtlib2\" \"(= x 1)\" smtlib \"(= x 1)\" sort \"Bool\"\n"
        ), "{text}");
        assert!(
            text.contains(&format!(
                "\ncertificate 0 \"clean\" clean_cic [1] [2] \"sha256\" [{zeros}]\n"
            )),
            "{text}"
        );
        round_trip_eq(&module);
    }

    /// The v46 typed spec carrier: `var .. sort`, `invariant .. typed`, and
    /// every `TemporalForm` (fairness with and without its relation).
    #[test]
    fn ws44_spec_carrier_round_trips_exactly() {
        use crate::proof::{ClausePlace, ClauseSort, ProofFormula};
        let leaf = |payload: &str, place| {
            ws44_bound("smtlib2", payload, vec![("x", ClauseSort::Int, place)])
        };
        let mut sm = SpecModule::linked("ring");
        sm.vars
            .push(SpecVar::new("x", "Int").with_sort(ClauseSort::Int));
        sm.vars.push(SpecVar::new("y", "0..7"));
        sm.actions.push("Step".into());
        sm.invariants.push(
            SpecInvariant::new("Pos", "(>= x 0)")
                .with_typed(leaf("(>= x 0)", ClausePlace::SpecVar { index: 0 })),
        );
        sm.invariants.push(SpecInvariant::new("Untyped", "true"));
        sm.temporal = vec![
            SpecTemporal::new(
                "A",
                TemporalForm::Always(leaf("(>= x 0)", ClausePlace::SpecVar { index: 0 })),
            ),
            SpecTemporal::new(
                "E",
                TemporalForm::Eventually(leaf("(= x 7)", ClausePlace::SpecVar { index: 0 })),
            ),
            SpecTemporal::new(
                "L",
                TemporalForm::LeadsTo(
                    leaf("(= x 0)", ClausePlace::SpecVar { index: 0 }),
                    ProofFormula::smtlib2("true", "Bool"),
                ),
            ),
            SpecTemporal::new(
                "W",
                TemporalForm::WeakFair {
                    action: "Step".into(),
                    relation: Some(leaf(
                        "(= x' (+ x 1))",
                        ClausePlace::SpecVarNext { index: 0 },
                    )),
                },
            ),
            SpecTemporal::new(
                "S",
                TemporalForm::StrongFair {
                    action: "Step".into(),
                    relation: None,
                },
            ),
        ];
        let mut module = Module::new("spec");
        module.spec_modules.push(sm);
        assert!(crate::text_loss::text_losses(&module).is_empty());
        let text = format!("{module}");
        for needle in [
            "  var \"x\" : \"Int\" sort int\n",
            "  var \"y\" : \"0..7\"\n",
            "  invariant \"Pos\" : \"(>= x 0)\" typed formula \"smtlib2\" \"(>= x 0)\" bind \"x\" int spec_var(0)\n",
            "  temporal \"L\" leads_to formula \"smtlib2\" \"(= x 0)\" bind \"x\" int spec_var(0) formula \"smtlib2\" \"true\" smtlib \"true\" sort \"Bool\"\n",
            "  temporal \"W\" weak_fair \"Step\" formula ",
            "spec_var_next(0)",
            "  temporal \"S\" strong_fair \"Step\"\n",
        ] {
            assert!(text.contains(needle), "missing {needle:?} in:\n{text}");
        }
        round_trip_eq(&module);
    }

    /// The depth cap: a sort nested exactly [`MAX_TEXT_CLAUSE_SORT_DEPTH`]
    /// deep round-trips; one level deeper is REPORTED by `text_losses` (so
    /// the printer marks the text `#lossy`) and refused by the reader — the
    /// printer never writes a sort its own reader refuses unmarked.
    #[test]
    fn ws44_clause_sort_depth_cap_is_reported_not_printed_unmarked() {
        use crate::proof::{ClausePlace, ClauseSort, ProofObligation, ProofStatus};
        use crate::text_loss::{MAX_TEXT_CLAUSE_SORT_DEPTH, TextLossKind, clause_sort_depth};
        use crate::value::ProofId;
        let nested = |depth: usize| {
            let mut sort = ClauseSort::Bool;
            for _ in 1..depth {
                sort = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(sort));
            }
            sort
        };
        let module_with = |depth: usize| {
            let mut module = Module::new("deep");
            module.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(0),
                    crate::proof::ObligationKind::Postcondition,
                    ProofStatus::Pending,
                    "d",
                )
                .with_formula(ws44_bound(
                    "smtlib2",
                    "x",
                    vec![("x", nested(depth), ClausePlace::World)],
                )),
            );
            module
        };
        assert_eq!(clause_sort_depth(&nested(MAX_TEXT_CLAUSE_SORT_DEPTH)), 64);
        round_trip_eq(&module_with(MAX_TEXT_CLAUSE_SORT_DEPTH));
        let deep = module_with(MAX_TEXT_CLAUSE_SORT_DEPTH + 1);
        assert_lossy_refused(&deep, &[TextLossKind::ClauseBindings]);
        // The reader refuses the deep sort by name even with the marker gone.
        let unmarked: String = format!("{deep}")
            .lines()
            .filter(|line| !line.starts_with("; #lossy:"))
            .map(|line| format!("{line}\n"))
            .collect();
        refused(&unmarked, "clause sort nests deeper than 64 levels");
        // The same cap on a summary clause and a spec carrier.
        let mut summary = Module::new("deep_summary");
        let ft = summary
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        summary.functions.push(Function::declaration(
            FuncId::new(0),
            "f",
            ft,
            FunctionSummary::new().ensuring(ws44_bound(
                "smtlib2",
                "x",
                vec![("x", nested(65), ClausePlace::World)],
            )),
        ));
        assert_lossy_refused(&summary, &[TextLossKind::FunctionSummary]);
        let mut spec = Module::new("deep_spec");
        let mut machine = SpecModule::linked("m");
        machine
            .vars
            .push(SpecVar::new("x", "Int").with_sort(nested(65)));
        spec.spec_modules.push(machine);
        assert_lossy_refused(&spec, &[TextLossKind::SpecCarrier]);
    }

    /// Negative twins for the summary block: a clause line with no preceding
    /// `#summary`, an out-of-order block, a second `#summary`, a second
    /// `#backed-by`, and a non-contiguous block are each a named
    /// `ParseError`, never a silently rearranged summary.
    #[test]
    fn ws44_summary_block_grammar_is_strict() {
        let mut module = build_add_module();
        module.functions[0].summary = Some(
            FunctionSummary::new()
                .with_params(vec!["a".into(), "b".into()])
                .requiring(crate::proof::ProofFormula::smtlib2("(> a 0)", "Bool"))
                .ensuring(crate::proof::ProofFormula::smtlib2("(> r 0)", "Bool")),
        );
        module.functions[0]
            .proofs
            .push(crate::proof::ProofAnnotation::Pure);
        let text = format!("{module}");
        assert_eq!(parse_module(&text).expect("control parses"), module);
        let header = "    ; #summary: unproved params [\"a\", \"b\"]\n";
        let requires =
            "    ; #requires: formula \"smtlib2\" \"(> a 0)\" smtlib \"(> a 0)\" sort \"Bool\"\n";
        let ensures =
            "    ; #ensures: formula \"smtlib2\" \"(> r 0)\" smtlib \"(> r 0)\" sort \"Bool\"\n";
        assert!(
            text.contains(&format!("{header}{requires}{ensures}")),
            "{text}"
        );

        // `; #requires:` without a preceding `#summary`.
        refused(
            &text.replacen(header, "", 1),
            "`#requires` without a preceding `#summary` directive",
        );
        // Out of order.
        refused(
            &text.replacen(
                &format!("{requires}{ensures}"),
                &format!("{ensures}{requires}"),
                1,
            ),
            "`#requires` out of order in the #summary block",
        );
        // A second header.
        refused(
            &text.replacen(header, &format!("{header}{header}"), 1),
            "duplicate #summary directive",
        );
        // A second `#backed-by`.
        let backed = "    ; #backed-by: extern 0 \"x\" none\n";
        refused(
            &text.replacen(ensures, &format!("{ensures}{backed}{backed}"), 1),
            "duplicate #backed-by directive",
        );
        // Not contiguous: another directive splits the block.
        refused(
            &text.replacen(ensures, &format!("    ; #producer: trust\n{ensures}"), 1),
            "`#ensures` after the summary block ended",
        );
        // The diagnostic `Display` spelling of a custom kind is not the
        // module-text spelling and is refused.
        let custom =
            "; TrustIr text format v1\nmodule \"m\"\n\nobligation 0 custom:ns/name pending \"d\"\n";
        refused(custom, "expected '(', got ':'");
    }

    /// Review twins (WS4.4): each new clause of the proof-surface grammar is
    /// refused BY NAME when malformed — never read as something else, never
    /// silently dropped. The control line parses, so each twin differs from
    /// an accepted text by exactly the one edit it names.
    #[test]
    fn ws44_proof_surface_grammar_twins_are_refused_by_name() {
        let zeros = vec!["0"; 32].join(", ");
        let head = "; TrustIr text format v1\nmodule \"m\"\n\n";
        let obligation = |tail: &str| {
            format!(
                "{head}obligation 0 postcondition pending \"d\" formula \"smtlib2\" \"x\"{tail}\n"
            )
        };
        let certificate = |tail: &str| {
            format!(
                "{head}obligation 0 postcondition pending \"d\"\ncertificate 0 \"p\" \
                 clean_cic [1] [2] \"sha256\" [{zeros}]{tail}\n"
            )
        };
        // Controls: each clause parses in its accepted spelling.
        let bound = parse_module(&obligation(" bind \"x\" int world")).expect("control");
        assert_eq!(
            bound.proof_obligations[0]
                .formula
                .as_ref()
                .unwrap()
                .bindings
                .len(),
            1
        );
        let recheck = format!(
            " recheck module \"M\" anchor \"a\" theorems [] axioms [] binding env \"sha256\" \
             [{zeros}] statement \"sha256\" [{zeros}] callees [] island [1, 2] \"sha256\" [{zeros}]"
        );
        let checked = parse_module(&certificate(&recheck)).expect("control");
        assert!(matches!(
            &checked.proof_certificates[0].evidence,
            crate::proof::ProofEvidence::CleanCic { kernel_recheck: Some(r), .. }
                if r.binding.as_ref().is_some_and(|b| b.environment.is_some())
        ));
        parse_module(&certificate(&format!(
            " assurance unwind(3) digest \"sha256\" [{zeros}]"
        )))
        .expect("control");

        // An unknown sort word, an unknown place word, an unknown bound.
        refused(
            &obligation(" bind \"x\" integer world"),
            "unknown clause sort 'integer'",
        );
        refused(
            &obligation(" bind \"x\" int heap"),
            "unknown clause place 'heap'",
        );
        refused(
            &certificate(&format!(" assurance bounded digest \"sha256\" [{zeros}]")),
            "unknown coverage bound 'bounded'",
        );
        // A `bind` clause is matched on its item's line only: one pushed onto
        // the next line is an unknown top-level line, not a binding of the
        // obligation above it.
        refused(
            &obligation("\nbind \"x\" int world"),
            "unknown directive `bind` — refusing rather than dropping it",
        );
        // So are the formula's other trailing clauses: a `sort` line below it
        // is not its sort, and a `bind` behind a next-line `smtlib` is not
        // reached by skipping the newline the `smtlib` probe crossed.
        refused(
            &obligation("\nsort \"Bool\""),
            "unknown directive `sort` — refusing rather than dropping it",
        );
        refused(
            &obligation("\nsmtlib \"x\" bind \"x\" int world"),
            "unknown directive `smtlib` — refusing rather than dropping it",
        );
        // Control: the same clauses on the formula's line are read.
        let same_line = parse_module(&obligation(
            " smtlib \"x\" sort \"Bool\" bind \"x\" int world",
        ))
        .expect("control");
        let formula = same_line.proof_obligations[0].formula.as_ref().unwrap();
        assert_eq!(
            (
                formula.smtlib.as_deref(),
                formula.sort.as_deref(),
                formula.bindings.len()
            ),
            (Some("x"), Some("Bool"), 1)
        );
        // The recheck clause's fixed order: `anchor` cannot be skipped.
        refused(
            &certificate(" recheck module \"M\" theorems [] axioms []"),
            "expected 'anchor'",
        );
        // An island without its declaration bytes is not read as one.
        refused(
            &certificate(&recheck.replacen("island [1, 2]", "island", 1)),
            "expected '['",
        );
    }

    /// Mutation control 2: bindings are a `Vec`, and ORDER is identity (it
    /// enters the v6 lineage and the content digest). A text whose bind list
    /// is reversed parses to a DIFFERENT module, so a printer that reordered
    /// bindings would fail every structural-equality leg.
    #[test]
    fn ws44_binding_order_is_identity() {
        use crate::proof::{ClausePlace, ClauseSort, ProofObligation, ProofStatus};
        use crate::value::ProofId;
        let mut module = Module::new("order");
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                crate::proof::ObligationKind::Postcondition,
                ProofStatus::Pending,
                "d",
            )
            .with_formula(ws44_bound(
                "smtlib2",
                "(= a b)",
                vec![
                    ("a", ClauseSort::Int, ClausePlace::World),
                    ("b", ClauseSort::Bool, ClausePlace::Unwind),
                ],
            )),
        );
        let text = format!("{module}");
        let a = " bind \"a\" int world";
        let b_ = " bind \"b\" bool unwind";
        assert!(text.contains(&format!("{a}{b_}")), "{text}");
        let reversed = text.replacen(&format!("{a}{b_}"), &format!("{b_}{a}"), 1);
        let parsed = parse_module(&reversed).expect("a reversed bind list still parses");
        assert_ne!(
            parsed, module,
            "a reordered bind list must not decode to the same module"
        );
        round_trip_eq(&module);
    }
}
