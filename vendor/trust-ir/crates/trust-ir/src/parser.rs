// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive-descent parser for TrustIr text format.
//!
//! Parses the exact format produced by the Display implementations in display.rs.
//! Round-trip property: Display -> parse -> Display produces identical output.

use crate::constant::Constant;
use crate::inst::*;
use crate::node::InstrNode;
use crate::proof::{
    DiagnosticSeverity, Divergence, ObligationDiagnostic, ObligationKind, ProofAnnotation,
    ProofCertificate, ProofContext, ProofDigest, ProofDigestAlgorithm, ProofEvidence, ProofFormula,
    ProofObligation, ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
    PublicObligationIdentity,
};
use crate::spec::{
    ProofKind, SpecAnchor, SpecInvariant, SpecModule, SpecOrigin, SpecProof, SpecVar, SpecWaiver,
};
use crate::ty::{EnumDef, EnumVariant, FatPtrKind, FieldDef, FuncTy, SetRepr, StructDef, Ty};
use crate::value::{
    BindingFrameId, BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, GlobalId, ProofId, ProofTag,
    RecordId, ScopeData, SourceSpan, StructId, TyId, ValueId,
};
use crate::{
    Block, CallingConv, Endianness, Function, Global, Linkage, Module, Producer,
    SourceBindingProvenance, SourceLoopProvenance, SourcePlace, SourceProvenance, TargetInfo,
    TlsModel,
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

/// Internal parser state.
struct Parser<'a> {
    input: &'a str,
    pos: usize,
    line: usize,
    col: usize,
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

    fn advance(&mut self, n: usize) {
        for ch in self.input[self.pos..self.pos + n].chars() {
            if ch == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        self.pos += n;
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_whitespace() {
                self.advance(1);
            } else {
                break;
            }
        }
    }

    fn skip_whitespace_no_newline(&mut self) {
        while let Some(ch) = self.peek_char() {
            if ch == ' ' || ch == '\t' {
                self.advance(1);
            } else {
                break;
            }
        }
    }

    fn skip_line(&mut self) {
        while let Some(ch) = self.peek_char() {
            self.advance(1);
            if ch == '\n' {
                break;
            }
        }
    }

    fn expect_str(&mut self, s: &str) -> Result<(), ParseError> {
        self.skip_whitespace();
        if self.remaining().starts_with(s) {
            self.advance(s.len());
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
            self.advance(s.len());
            true
        } else {
            false
        }
    }

    /// v25 Bytes: one hex digit (0-9a-fA-F) -> its value.
    fn expect_hex_digit(&mut self) -> Result<u8, ParseError> {
        match self.peek_char() {
            Some(c) if c.is_ascii_hexdigit() => {
                self.advance(c.len_utf8());
                Ok(c.to_digit(16).expect("hexdigit checked") as u8)
            }
            other => Err(self.error(format!(
                "expected hex digit in bytes constant, got {other:?}"
            ))),
        }
    }

    fn expect_char(&mut self, ch: char) -> Result<(), ParseError> {
        self.skip_whitespace();
        match self.peek_char() {
            Some(c) if c == ch => {
                self.advance(c.len_utf8());
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
            self.advance(s.len());
            true
        } else {
            self.pos = saved_pos;
            self.line = saved_line;
            self.col = saved_col;
            false
        }
    }

    /// Read an identifier (alphanumeric + underscores + dots).
    fn read_ident(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            // `$` is admitted so linker-symbol spellings round-trip through the
            // text codec: Darwin symbol variants (`opendir$INODE64`), TLV init
            // templates (`X$tlv$init`), and legacy-mangled Rust symbols
            // (`_$LT$`, `$u20$`). It is never a syntactic token in this format, so
            // widening the identifier set here cannot change any existing parse.
            if ch.is_alphanumeric() || ch == '_' || ch == '.' || ch == '$' {
                self.advance(1);
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

    /// Read a quoted string (as produced by Rust's {:?} for strings).
    fn read_quoted_string(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        self.expect_char('"')?;
        let mut result = String::new();
        loop {
            match self.peek_char() {
                None => return Err(self.error("unterminated string")),
                Some('"') => {
                    self.advance(1);
                    return Ok(result);
                }
                Some('\\') => {
                    self.advance(1);
                    match self.peek_char() {
                        Some('"') => {
                            self.advance(1);
                            result.push('"');
                        }
                        Some('\\') => {
                            self.advance(1);
                            result.push('\\');
                        }
                        Some('n') => {
                            self.advance(1);
                            result.push('\n');
                        }
                        Some('t') => {
                            self.advance(1);
                            result.push('\t');
                        }
                        // Full control-char escape decoding (finding F): `\r`,
                        // `\0`, and `\u{HEX}` for any other control character.
                        Some('r') => {
                            self.advance(1);
                            result.push('\r');
                        }
                        Some('0') => {
                            self.advance(1);
                            result.push('\0');
                        }
                        Some('u') => {
                            self.advance(1);
                            self.expect_char('{')?;
                            let start = self.pos;
                            while let Some(ch) = self.peek_char() {
                                if ch.is_ascii_hexdigit() {
                                    self.advance(1);
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
                            self.advance(c.len_utf8());
                            result.push(c);
                        }
                        None => return Err(self.error("unterminated escape")),
                    }
                }
                Some(ch) => {
                    self.advance(ch.len_utf8());
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
                self.advance(1);
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
                self.advance(1);
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
            self.advance(1);
        }
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.advance(1);
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
            self.advance(1);
        }
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.advance(1);
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
                self.advance(1);
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

    /// Try to parse ", align N" suffix. Returns Ok(Some(n)) if present.
    fn try_parse_align(&mut self) -> Result<Option<u64>, ParseError> {
        let saved_pos = self.pos;
        let saved_line = self.line;
        let saved_col = self.col;
        if self.try_str(",") {
            self.skip_whitespace_no_newline();
            if self.remaining().starts_with("align ") {
                self.advance(6);
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
    fn try_parse_linkage(&mut self) -> Linkage {
        self.skip_whitespace();
        let rem = self.remaining();
        if rem.starts_with("internal ") {
            self.advance(9);
            Linkage::Internal
        } else if rem.starts_with("private ") {
            self.advance(8);
            Linkage::Private
        } else if rem.starts_with("weak ") {
            self.advance(5);
            Linkage::Weak
        } else if rem.starts_with("linkonce ") {
            self.advance(9);
            Linkage::LinkOnce
        } else if rem.starts_with("external ") {
            self.advance(9);
            Linkage::External
        } else {
            Linkage::External
        }
    }

    /// Try to parse global TLS metadata: tls(<model>).
    fn try_parse_tls_model(&mut self) -> Result<Option<TlsModel>, ParseError> {
        self.skip_whitespace();
        if !self.remaining().starts_with("tls(") {
            return Ok(None);
        }
        self.advance(3);
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
    fn try_parse_calling_conv(&mut self) -> CallingConv {
        self.skip_whitespace();
        let rem = self.remaining();
        if rem.starts_with("fastcc ") {
            self.advance(7);
            CallingConv::Fast
        } else if rem.starts_with("coldcc ") {
            self.advance(7);
            CallingConv::Cold
        } else if rem.starts_with("rustcc ") {
            self.advance(7);
            CallingConv::Rust
        } else if rem.starts_with("swiftcc ") {
            self.advance(8);
            CallingConv::Swift
        } else if rem.starts_with("ccc ") {
            self.advance(4);
            CallingConv::C
        } else {
            CallingConv::C
        }
    }

    /// Parse a type.
    fn parse_ty(&mut self) -> Result<Ty, ParseError> {
        self.skip_whitespace();
        let rem = self.remaining();

        // Reference types
        if rem.starts_with("&mut ") {
            self.advance(5); // "&mut "
            let inner = self.parse_ty()?;
            return Ok(Ty::RefMut(Box::new(inner)));
        }
        if rem.starts_with('&') && !rem.starts_with("&&") {
            // Simple &T (not &&T which would be &(&T))
            self.advance(1);
            let inner = self.parse_ty()?;
            return Ok(Ty::Ref(Box::new(inner)));
        }
        if rem.starts_with("&&") {
            // &&T = &(&T)
            self.advance(1); // consume first &
            let inner = self.parse_ty()?;
            return Ok(Ty::Ref(Box::new(inner)));
        }
        if rem.starts_with("*const ") {
            self.advance(7);
            let inner = self.parse_ty()?;
            return Ok(Ty::PtrConst(Box::new(inner)));
        }
        if rem.starts_with("*mut ") {
            self.advance(5);
            let inner = self.parse_ty()?;
            return Ok(Ty::PtrMut(Box::new(inner)));
        }
        if rem.starts_with("Rc<") {
            self.advance(3);
            let inner = self.parse_ty()?;
            self.expect_char('>')?;
            return Ok(Ty::Rc(Box::new(inner)));
        }
        if rem.starts_with('!') {
            self.advance(1);
            return Ok(Ty::Never);
        }

        // Fat pointer: fatptr<str> | fatptr<slice ty.N> | fatptr<dyn.N>
        if rem.starts_with("fatptr<") {
            self.advance(7);
            if self.try_str("str") {
                self.expect_char('>')?;
                return Ok(Ty::FatPtr(FatPtrKind::Str));
            }
            if self.try_str("slice") {
                self.expect_str("ty.")?;
                let elem_id = self.read_u32()?;
                self.expect_char('>')?;
                return Ok(Ty::FatPtr(FatPtrKind::Slice(TyId::new(elem_id))));
            }
            self.expect_str("dyn.")?;
            let trait_id = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(Ty::FatPtr(FatPtrKind::TraitObject { trait_id }));
        }

        // Set: set<ty.N, bitset|boxed>
        if rem.starts_with("set<") {
            self.advance(4);
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
            return Ok(Ty::Set(TyId::new(elem_id), repr));
        }

        // Sequence: seq<ty.N>
        if rem.starts_with("seq<") {
            self.advance(4);
            self.expect_str("ty.")?;
            let elem_id = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(Ty::Sequence(TyId::new(elem_id)));
        }

        // Fixed-width vector: <N x Ty>
        if rem.starts_with('<') {
            self.advance(1);
            let lanes = self.read_u32()?;
            if lanes == 0 {
                return Err(self.error("vector lane count must be nonzero"));
            }
            self.expect_str("x")?;
            let elem = self.parse_ty()?;
            self.expect_char('>')?;
            return Ok(Ty::Vector(Box::new(elem), lanes));
        }

        // Unit `()`, zero-element tuple `(,)`, or tuple `(T, ...)`.
        if rem.starts_with('(') {
            self.advance(1);
            self.skip_whitespace();
            if self.try_str(")") {
                // `()` is the unit type, distinct from the empty tuple.
                return Ok(Ty::Unit);
            }
            if self.try_str(",") {
                // `(,)` is the zero-element tuple.
                self.skip_whitespace();
                self.expect_char(')')?;
                return Ok(Ty::Tuple(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_ty()?);
            while self.try_str(",") {
                elems.push(self.parse_ty()?);
            }
            self.expect_char(')')?;
            return Ok(Ty::Tuple(elems));
        }

        // Array: [ty.N x M]
        if rem.starts_with('[') {
            self.advance(1);
            self.expect_str("ty.")?;
            let elem_id = self.read_u32()?;
            self.expect_str("x")?;
            let len = self.read_u64()?;
            self.expect_char(']')?;
            return Ok(Ty::Array(TyId::new(elem_id), len));
        }

        // Refinement: refine<ty.N, pred.M> (v30 typed value model).
        if rem.starts_with("refine<") {
            self.advance(7);
            self.expect_str("ty.")?;
            let base = self.read_u32()?;
            self.expect_char(',')?;
            self.expect_str("pred.")?;
            let pred = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(Ty::Refine(TyId::new(base), crate::value::PredId::new(pred)));
        }

        // Keywords / compound type names
        let ident = self.read_ident()?;
        match ident.as_str() {
            "i8" => Ok(Ty::I8),
            "i16" => Ok(Ty::I16),
            "i32" => Ok(Ty::I32),
            "i64" => Ok(Ty::I64),
            "i128" => Ok(Ty::I128),
            // v25 B1 scalars. Ty::Error has NO parseable spelling (it is
            // producer-internal; its Display form "{error}" is deliberately
            // lexically invalid here) - fail closed.
            "isize" => Ok(Ty::Isize),
            "usize" => Ok(Ty::Usize),
            "char" => Ok(Ty::Char),
            "u8" => Ok(Ty::U8),
            "u16" => Ok(Ty::U16),
            "u32" => Ok(Ty::U32),
            "u64" => Ok(Ty::U64),
            "u128" => Ok(Ty::U128),
            "f16" => Ok(Ty::F16),
            "f32" => Ok(Ty::F32),
            "f64" => Ok(Ty::F64),
            "bool" => Ok(Ty::Bool),
            "ptr" => Ok(Ty::Ptr),
            "!" => Ok(Ty::Never),
            s if s.starts_with("struct.") => {
                let id: u32 = s[7..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid struct id: '{}'", s)))?;
                Ok(Ty::Struct(StructId::new(id)))
            }
            s if s.starts_with("enum.") => {
                let id: u32 = s[5..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid enum id: '{}'", s)))?;
                Ok(Ty::Enum(crate::value::EnumId::new(id)))
            }
            s if s.starts_with("functy.") => {
                let id: u32 = s[7..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid functy id: '{}'", s)))?;
                Ok(Ty::Func(FuncTyId::new(id)))
            }
            s if s.starts_with("record.") => {
                let id: u32 = s[7..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid record id: '{}'", s)))?;
                Ok(Ty::Record(RecordId::new(id)))
            }
            s if s.starts_with("closure.") => {
                let id: u32 = s[8..]
                    .parse()
                    .map_err(|_| self.error(format!("invalid closure id: '{}'", s)))?;
                Ok(Ty::Closure(ClosureTyId::new(id)))
            }
            other => Err(self.error(format!("unknown type: '{}'", other))),
        }
    }

    /// Parse a constant value.
    fn parse_constant(&mut self) -> Result<Constant, ParseError> {
        self.skip_whitespace();
        let rem = self.remaining();

        // Aggregate: { ... }
        if rem.starts_with('{') {
            self.advance(1);
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(Constant::Aggregate(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("}")?;
            return Ok(Constant::Aggregate(elems));
        }

        // Array: array[ ... ]
        if rem.starts_with("array[") {
            self.advance(6);
            self.skip_whitespace();
            if self.try_str("]") {
                return Ok(Constant::Array(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("]")?;
            return Ok(Constant::Array(elems));
        }

        // Vector: vec[ ... ]
        if rem.starts_with("vec[") {
            self.advance(4);
            self.skip_whitespace();
            if self.try_str("]") {
                return Ok(Constant::Vector(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("]")?;
            return Ok(Constant::Vector(elems));
        }

        // Sequence: seq[ ... ]
        if rem.starts_with("seq[") {
            self.advance(4);
            self.skip_whitespace();
            if self.try_str("]") {
                return Ok(Constant::Sequence(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("]")?;
            return Ok(Constant::Sequence(elems));
        }

        // Set: set{ ... }
        if rem.starts_with("set{") {
            self.advance(4);
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(Constant::Set(vec![]));
            }
            let mut elems = Vec::new();
            elems.push(self.parse_constant()?);
            while self.try_str(",") {
                elems.push(self.parse_constant()?);
            }
            self.expect_str("}")?;
            return Ok(Constant::Set(elems));
        }

        // Record: record{ name = val, ... }
        if rem.starts_with("record{") {
            self.advance(7);
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(Constant::Record(vec![]));
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
            return Ok(Constant::Record(fields));
        }

        // Closure: closure<func.N>{ c1, c2 }
        if rem.starts_with("closure<func.") {
            self.advance(13);
            let func_id = self.read_u32()?;
            self.expect_char('>')?;
            self.skip_whitespace();
            self.expect_char('{')?;
            self.skip_whitespace();
            if self.try_str("}") {
                return Ok(Constant::Closure {
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
            return Ok(Constant::Closure {
                func: FuncId::new(func_id),
                captures,
            });
        }

        // Bare function item: fndef<func.N>
        if rem.starts_with("fndef<func.") {
            self.advance(11);
            let func_id = self.read_u32()?;
            self.expect_char('>')?;
            return Ok(Constant::FnDef(FuncId::new(func_id)));
        }

        // v25 Bytes: `bytes<hex>` / `utf8bytes<hex>` — hex payload, two hex
        // digits per byte (the Display form; injective for every byte value).
        // The utf8 claim is CHECKED here, mirroring the binary decoder.
        if rem.starts_with("bytes<") || rem.starts_with("utf8bytes<") {
            let utf8 = rem.starts_with("utf8bytes<");
            self.advance(if utf8 { 10 } else { 6 });
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
            return Ok(Constant::Bytes { data, utf8 });
        }

        // Relocatable symbol address: symaddr<name> or symaddr<name + addend>.
        // The `name` is an identifier (function or data-global symbol) and the
        // optional `addend` is a signed integer byte offset. Mirrors the
        // `Display` form so text round-trips.
        if rem.starts_with("symaddr<") {
            self.advance(8);
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
            return Ok(Constant::SymbolAddr { symbol, addend });
        }

        if rem.starts_with("phantomdata")
            && !rem
                .get(11..12)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            self.advance(11);
            return Ok(Constant::PhantomData);
        }

        // Bool
        if rem.starts_with("true")
            && !rem
                .get(4..5)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric())
        {
            self.advance(4);
            return Ok(Constant::Bool(true));
        }
        if rem.starts_with("false")
            && !rem
                .get(5..6)
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_alphanumeric())
        {
            self.advance(5);
            return Ok(Constant::Bool(false));
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
    fn parse_number(&mut self) -> Result<Constant, ParseError> {
        self.skip_whitespace();

        // Non-finite float tokens. Checked before the digit-based
        // lexer so `inf` / `-inf` / `NaN` are never accidentally
        // treated as malformed integer literals.
        if self.try_str("NaN") {
            return Ok(Constant::Float(f64::NAN));
        }
        if self.try_str("inf") {
            return Ok(Constant::Float(f64::INFINITY));
        }
        if self.remaining().starts_with("-inf") {
            self.advance(4);
            return Ok(Constant::Float(f64::NEG_INFINITY));
        }

        let start = self.pos;
        let mut is_float = false;

        // Optional leading minus
        if self.peek_char() == Some('-') {
            self.advance(1);
        }

        // Integer part
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.advance(1);
            } else {
                break;
            }
        }

        // Decimal part?
        if self.peek_char() == Some('.') {
            is_float = true;
            self.advance(1);
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.advance(1);
                } else {
                    break;
                }
            }
        }

        // Exponent?
        if let Some('e' | 'E') = self.peek_char() {
            is_float = true;
            self.advance(1);
            if self.peek_char() == Some('-') || self.peek_char() == Some('+') {
                self.advance(1);
            }
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.advance(1);
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
            Ok(Constant::Float(v))
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
                return Ok(Constant::Int(v));
            }
            if !s.starts_with('-')
                && let Ok(v) = s.parse::<u128>()
            {
                debug_assert!(v > i128::MAX as u128);
                return Ok(Constant::U128(v));
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
            "shl" => Some(BinOp::Shl),
            "lshr" => Some(BinOp::LShr),
            "ashr" => Some(BinOp::AShr),
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
            self.advance(1);
        }
        // Integer part
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.advance(1);
            } else {
                break;
            }
        }
        // Decimal part
        if self.peek_char() == Some('.') {
            self.advance(1);
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.advance(1);
                } else {
                    break;
                }
            }
        }
        // Exponent
        if let Some('e' | 'E') = self.peek_char() {
            self.advance(1);
            if self.peek_char() == Some('-') || self.peek_char() == Some('+') {
                self.advance(1);
            }
            while let Some(ch) = self.peek_char() {
                if ch.is_ascii_digit() {
                    self.advance(1);
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
    /// An unrecognized `;` comment is skipped to end-of-line (back-compat).
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
            self.try_str(";");
            self.skip_whitespace_no_newline();
            if self.try_str("#proof:") {
                proofs.push(self.parse_proof_annotation()?);
                while self.try_str(",") {
                    proofs.push(self.parse_proof_annotation()?);
                }
            } else if self.try_str("#proof_ctx:") {
                proof_context = Some(self.parse_proof_context_clause()?);
            } else if self.try_str("#loc:") {
                span = Some(self.parse_loc_clause()?);
            } else if self.try_str("#scope:") {
                scope = Some(self.read_u32()?);
            } else {
                // Unknown comment: skip the rest of the line and stop.
                self.skip_line();
                break;
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
    fn parse_instruction(&mut self) -> Result<Inst, ParseError> {
        self.skip_whitespace();
        let rem = self.remaining();

        // Instructions that start with a keyword, in order of specificity.

        // "null ptr"
        if rem.starts_with("null ") {
            self.advance(5);
            self.expect_str("ptr")?;
            return Ok(Inst::NullPtr);
        }

        // "global_addr @global.N"
        if rem.starts_with("global_addr ") {
            self.advance(12);
            self.expect_str("@global.")?;
            let id = self.read_u32()?;
            return Ok(Inst::GlobalAddr {
                global: GlobalId::new(id),
            });
        }

        // "unreachable"
        if rem.starts_with("unreachable") {
            self.advance(11);
            return Ok(Inst::Unreachable);
        }

        // "ret ..."
        if rem.starts_with("ret")
            && rem[3..]
                .chars()
                .next()
                .is_none_or(|c| !c.is_alphanumeric() && c != '_' && c != '.')
        {
            self.advance(3);
            let mut values = Vec::new();
            self.skip_whitespace_no_newline();
            // Check if there are values following
            if self.peek_char() == Some('%') {
                values.push(self.read_value_id()?);
                while self.try_str(",") {
                    values.push(self.read_value_id()?);
                }
            }
            return Ok(Inst::Return { values });
        }

        // "br bb..."
        if rem.starts_with("br ") && !rem.starts_with("borrow") {
            self.advance(3);
            let target = self.read_block_id()?;
            let args = self.read_block_args()?;
            return Ok(Inst::Br { target, args });
        }

        // "condbr ..."
        if rem.starts_with("condbr ") {
            self.advance(7);
            let cond = self.read_value_id()?;
            self.expect_char(',')?;
            let then_target = self.read_block_id()?;
            let then_args = self.read_block_args()?;
            self.expect_char(',')?;
            let else_target = self.read_block_id()?;
            let else_args = self.read_block_args()?;
            return Ok(Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            });
        }

        // "switch ..."
        if rem.starts_with("switch ") {
            self.advance(7);
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
            return Ok(Inst::Switch {
                value,
                default,
                default_args,
                cases,
                // Parsed text IR never asserts the exhaustiveness fact; the
                // sound default keeps the otherwise arm reachable.
                exhaustive_enum_unreachable: false,
            });
        }

        // "call @func.N(...)"
        if rem.starts_with("call @func.") {
            self.advance(11);
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
            return Ok(Inst::Call {
                callee: FuncId::new(func_id),
                args,
            });
        }

        // "call_indirect %N(functy.M)(args...)"
        if rem.starts_with("call_indirect ") {
            self.advance(14);
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
            // Optional indirect-call ABI: ` cc=<conv>` (default C when absent).
            let mut calling_conv = CallingConv::default();
            self.skip_whitespace_no_newline();
            if self.remaining().starts_with("cc=") {
                self.advance(3);
                let tok = self.read_ident()?;
                calling_conv = match tok.as_str() {
                    "ccc" => CallingConv::C,
                    "fastcc" => CallingConv::Fast,
                    "coldcc" => CallingConv::Cold,
                    "rustcc" => CallingConv::Rust,
                    "swiftcc" => CallingConv::Swift,
                    other => {
                        return Err(self.error(format!("unknown calling convention: '{other}'")));
                    }
                };
            }
            return Ok(Inst::CallIndirect {
                callee,
                sig: FuncTyId::new(sig_id),
                args,
                calling_conv,
            });
        }

        // "icmp OP TY %a, %b"
        if rem.starts_with("icmp ") {
            self.advance(5);
            let op_name = self.read_ident()?;
            let op = Self::parse_icmpop(&op_name)
                .ok_or_else(|| self.error(format!("unknown icmp op: '{}'", op_name)))?;
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(Inst::ICmp { op, ty, lhs, rhs });
        }

        // "fcmp OP TY %a, %b"
        if rem.starts_with("fcmp ") {
            self.advance(5);
            let op_name = self.read_ident()?;
            let op = Self::parse_fcmpop(&op_name)
                .ok_or_else(|| self.error(format!("unknown fcmp op: '{}'", op_name)))?;
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(Inst::FCmp { op, ty, lhs, rhs });
        }

        // "[volatile] load TY, ptr %N[, align N]"
        if rem.starts_with("volatile load ") || rem.starts_with("load ") {
            let volatile = if rem.starts_with("volatile ") {
                self.advance(9); // "volatile "
                true
            } else {
                false
            };
            self.advance(5); // "load "
            let ty = self.parse_ty()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            let align = self.try_parse_align()?;
            return Ok(Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            });
        }

        // "[volatile] store TY %val, ptr %ptr[, align N]"
        if rem.starts_with("volatile store ") || rem.starts_with("store ") {
            let volatile = if rem.starts_with("volatile ") {
                self.advance(9); // "volatile "
                true
            } else {
                false
            };
            self.advance(6); // "store "
            let ty = self.parse_ty()?;
            let value = self.read_value_id()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            let align = self.try_parse_align()?;
            return Ok(Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            });
        }

        // "alloca TY[, %count][, align N]"
        if rem.starts_with("alloca ") {
            self.advance(7);
            let ty = self.parse_ty()?;
            // Parse optional count (starts with %) or align
            let mut count = None;
            let mut align = None;
            if self.try_str(",") {
                self.skip_whitespace_no_newline();
                if self.remaining().starts_with("align ") {
                    self.advance(6);
                    align = Some(self.read_u64()?);
                } else {
                    count = Some(self.read_value_id()?);
                    // After count, check for align
                    align = self.try_parse_align()?;
                }
            }
            return Ok(Inst::Alloca { ty, count, align });
        }

        // "heap_alloc ORIGIN TY[, %count][, align N]"
        if rem.starts_with("heap_alloc ") {
            self.advance(11);
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
                    self.advance(6);
                    align = Some(self.read_u64()?);
                } else {
                    count = Some(self.read_value_id()?);
                    align = self.try_parse_align()?;
                }
            }
            return Ok(Inst::HeapAlloc {
                ty,
                count,
                align,
                origin,
            });
        }

        // "gep [inbounds] TY, ptr %base, %idx..."
        if rem.starts_with("gep ") {
            self.advance(4);
            let inbounds = self.try_str("inbounds ");
            let pointee_ty = self.parse_ty()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let base = self.read_value_id()?;
            let mut indices = Vec::new();
            while self.try_str(",") {
                indices.push(self.read_value_id()?);
            }
            return Ok(Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            });
        }

        // "atomic_load ORDERING TY, ptr %N"
        if rem.starts_with("atomic_load ") {
            self.advance(12);
            let ordering = self.parse_ordering()?;
            let ty = self.parse_ty()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            return Ok(Inst::AtomicLoad { ty, ptr, ordering });
        }

        // "atomic_store ORDERING TY %val, ptr %ptr"
        if rem.starts_with("atomic_store ") {
            self.advance(13);
            let ordering = self.parse_ordering()?;
            let ty = self.parse_ty()?;
            let value = self.read_value_id()?;
            self.expect_char(',')?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            return Ok(Inst::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            });
        }

        // "atomicrmw OP ORDERING TY ptr %ptr, %val"
        if rem.starts_with("atomicrmw ") {
            self.advance(10);
            let op_name = self.read_ident()?;
            let op = Self::parse_atomicrmwop(&op_name)
                .ok_or_else(|| self.error(format!("unknown atomicrmw op: '{}'", op_name)))?;
            let ordering = self.parse_ordering()?;
            let ty = self.parse_ty()?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(Inst::AtomicRMW {
                op,
                ty,
                ptr,
                value,
                ordering,
            });
        }

        // "cmpxchg TY ptr %ptr, %expected, %desired SUCCESS FAILURE"
        if rem.starts_with("cmpxchg ") {
            self.advance(8);
            let ty = self.parse_ty()?;
            self.expect_str("ptr")?;
            let ptr = self.read_value_id()?;
            self.expect_char(',')?;
            let expected = self.read_value_id()?;
            self.expect_char(',')?;
            let desired = self.read_value_id()?;
            let success = self.parse_ordering()?;
            let failure = self.parse_ordering()?;
            return Ok(Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                success,
                failure,
            });
        }

        // "fence ORDERING"
        if rem.starts_with("fence ") {
            self.advance(6);
            let ordering = self.parse_ordering()?;
            return Ok(Inst::Fence { ordering });
        }

        // "const TY VALUE"
        if rem.starts_with("const ") {
            self.advance(6);
            let ty = self.parse_ty()?;
            let value = self.parse_constant()?;
            return Ok(Inst::Const { ty, value });
        }

        // "undef TY"
        if rem.starts_with("undef ") {
            self.advance(6);
            let ty = self.parse_ty()?;
            return Ok(Inst::Undef { ty });
        }

        // "copy TY %N"
        if rem.starts_with("copy ") {
            self.advance(5);
            let ty = self.parse_ty()?;
            let operand = self.read_value_id()?;
            return Ok(Inst::Copy { ty, operand });
        }

        // "seq_map_add_k TY %seq, K"  (loopFwd: for x in &mut l { *x += k })
        if rem.starts_with("seq_map_add_k ") {
            self.advance(14);
            let ty = self.parse_ty()?;
            let seq = self.read_value_id()?;
            self.expect_char(',')?;
            self.skip_whitespace_no_newline();
            let k = self.read_u64()?;
            return Ok(Inst::SeqMapAddK { ty, seq, k });
        }

        // "seq_map_not TY %seq"  (loopFwd: for b in &mut l { *b = !*b })
        if rem.starts_with("seq_map_not ") {
            self.advance(12);
            let ty = self.parse_ty()?;
            let seq = self.read_value_id()?;
            return Ok(Inst::SeqMapNot { ty, seq });
        }

        // "seq_map TY %seq, @func.N"  (general element-op loopFwd:
        // for x in &mut l { *x = fwd(x) }; fwd is a single-&mut element fn).
        // Placed after the longer seq_map_add_k / seq_map_not mnemonics; the
        // trailing space keeps the prefixes disjoint either way.
        if rem.starts_with("seq_map ") {
            self.advance(8);
            let ty = self.parse_ty()?;
            let seq = self.read_value_id()?;
            self.expect_char(',')?;
            self.skip_whitespace_no_newline();
            self.expect_str("@func.")?;
            let fwd = self.read_u32()?;
            return Ok(Inst::SeqMap {
                ty,
                seq,
                fwd: FuncId::new(fwd),
            });
        }

        // "select TY %cond, %then, %else"
        if rem.starts_with("select ") {
            self.advance(7);
            let ty = self.parse_ty()?;
            let cond = self.read_value_id()?;
            self.expect_char(',')?;
            let then_val = self.read_value_id()?;
            self.expect_char(',')?;
            let else_val = self.read_value_id()?;
            return Ok(Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            });
        }

        // "assume %N"
        if rem.starts_with("assume ") {
            self.advance(7);
            let cond = self.read_value_id()?;
            return Ok(Inst::Assume { cond });
        }

        // "assert %N"
        if rem.starts_with("assert ") {
            self.advance(7);
            let cond = self.read_value_id()?;
            return Ok(Inst::Assert { cond });
        }

        // "borrow_mut %N"
        if rem.starts_with("borrow_mut ") {
            self.advance(11);
            let ptr = self.read_value_id()?;
            return Ok(Inst::BorrowMut { ptr });
        }

        // "borrow %N" (check after borrow_mut)
        if rem.starts_with("borrow ") {
            self.advance(7);
            let ptr = self.read_value_id()?;
            return Ok(Inst::Borrow { ptr });
        }

        // "end_borrow %N"
        if rem.starts_with("end_borrow ") {
            self.advance(11);
            let borrow_ptr = self.read_value_id()?;
            return Ok(Inst::EndBorrow { borrow_ptr });
        }

        // "retain %N"
        if rem.starts_with("retain ") {
            self.advance(7);
            let ptr = self.read_value_id()?;
            return Ok(Inst::Retain { ptr });
        }

        // "release %N"
        if rem.starts_with("release ") {
            self.advance(8);
            let ptr = self.read_value_id()?;
            return Ok(Inst::Release { ptr });
        }

        // "is_unique %N"
        if rem.starts_with("is_unique ") {
            self.advance(10);
            let ptr = self.read_value_id()?;
            return Ok(Inst::IsUnique { ptr });
        }

        // "dealloc %N"
        if rem.starts_with("dealloc ") {
            self.advance(8);
            let ptr = self.read_value_id()?;
            return Ok(Inst::Dealloc { ptr });
        }

        // Binding-frame instructions. Syntax mirrors `display::write_inst`
        // (crates/trust_ir/src/display.rs:431-455) and is the canonical form
        // emitted by `format::canonical`.

        // `open_frame #<id> "<name>" {slot_name: TY, ...}`
        if rem.starts_with("open_frame ") {
            self.advance(11);
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
            return Ok(Inst::OpenFrame {
                def: BindingFrameDef::new(BindingFrameId::new(id), name, slots),
            });
        }

        // `bind_slot %frame, <slot>, %value`
        if rem.starts_with("bind_slot ") {
            self.advance(10);
            let frame = self.read_value_id()?;
            self.expect_char(',')?;
            let slot = self.read_u32()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(Inst::BindSlot { frame, slot, value });
        }

        // `load_slot <ty> %frame, <slot>`
        if rem.starts_with("load_slot ") {
            self.advance(10);
            let ty = self.parse_ty()?;
            let frame = self.read_value_id()?;
            self.expect_char(',')?;
            let slot = self.read_u32()?;
            return Ok(Inst::LoadSlot { frame, slot, ty });
        }

        // `close_frame %frame`
        if rem.starts_with("close_frame ") {
            self.advance(12);
            let frame = self.read_value_id()?;
            return Ok(Inst::CloseFrame { frame });
        }

        // `coro_suspend %frame, <state_slot>, <next_state>, %value`
        if rem.starts_with("coro_suspend ") {
            self.advance(13);
            let frame = self.read_value_id()?;
            self.expect_char(',')?;
            let state_slot = self.read_u32()?;
            self.expect_char(',')?;
            let next_state = self.read_i64()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(Inst::CoroSuspend {
                frame,
                state_slot,
                next_state,
                value,
            });
        }

        // "invoke @func.N(args) to bbNORMAL(normal_args) unwind bbUNWIND"
        if rem.starts_with("invoke @func.") {
            self.advance(13);
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
            return Ok(Inst::Invoke {
                callee: FuncId::new(func_id),
                args,
                normal_dest: BlockId::new(normal),
                normal_args,
                unwind_dest: BlockId::new(unwind),
            });
        }

        // "landingpad [cleanup] [catch i0, i1, ..]"
        if rem.starts_with("landingpad") {
            self.advance(10);
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
            return Ok(Inst::LandingPad {
                is_cleanup,
                catch_type_indices,
            });
        }

        // "resume %exn"
        if rem.starts_with("resume ") {
            self.advance(7);
            let exn = self.read_value_id()?;
            return Ok(Inst::Resume { exn });
        }

        // "extractfield TY %agg, FIELD"
        if rem.starts_with("extractfield ") {
            self.advance(13);
            let ty = self.parse_ty()?;
            let aggregate = self.read_value_id()?;
            self.expect_char(',')?;
            let field = self.read_u32()?;
            return Ok(Inst::ExtractField {
                ty,
                aggregate,
                field,
            });
        }

        // "insertfield TY %agg, FIELD, %val"
        if rem.starts_with("insertfield ") {
            self.advance(12);
            let ty = self.parse_ty()?;
            let aggregate = self.read_value_id()?;
            self.expect_char(',')?;
            let field = self.read_u32()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            });
        }

        // "extractelement TY %arr, %idx"
        if rem.starts_with("extractelement ") {
            self.advance(15);
            let ty = self.parse_ty()?;
            let array = self.read_value_id()?;
            self.expect_char(',')?;
            let index = self.read_value_id()?;
            return Ok(Inst::ExtractElement { ty, array, index });
        }

        // "insertelement TY %arr, %idx, %val"
        if rem.starts_with("insertelement ") {
            self.advance(14);
            let ty = self.parse_ty()?;
            let array = self.read_value_id()?;
            self.expect_char(',')?;
            let index = self.read_value_id()?;
            self.expect_char(',')?;
            let value = self.read_value_id()?;
            return Ok(Inst::InsertElement {
                ty,
                array,
                index,
                value,
            });
        }

        // "ptr_data PTR_TY %ptr"
        if rem.starts_with("ptr_data ") {
            self.advance(9);
            let ptr_ty = self.parse_ty()?;
            let ptr = self.read_value_id()?;
            return Ok(Inst::PtrData { ptr_ty, ptr });
        }

        // "ptr_metadata PTR_TY %ptr to META_TY"
        if rem.starts_with("ptr_metadata ") {
            self.advance(13);
            let ptr_ty = self.parse_ty()?;
            let ptr = self.read_value_id()?;
            self.expect_str("to")?;
            let metadata_ty = self.parse_ty()?;
            return Ok(Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            });
        }

        // "ptr_from_parts PTR_TY ptr %data, META_TY %metadata"
        if rem.starts_with("ptr_from_parts ") {
            self.advance(15);
            let ptr_ty = self.parse_ty()?;
            self.expect_str("ptr")?;
            let data = self.read_value_id()?;
            self.expect_char(',')?;
            let metadata_ty = self.parse_ty()?;
            let metadata = self.read_value_id()?;
            return Ok(Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            });
        }

        // "dialect_op <dialect>.<op>(%0, %1, ...) [-> TY | -> (TY, TY, ...)] [key=val]* [v<version>]"
        if rem.starts_with("dialect_op ") {
            self.advance(11);
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
            return Ok(Inst::Overflow { op, ty, lhs, rhs });
        }

        // BinOp: "add TY %a, %b"
        if let Some(op) = Self::parse_binop(&opname) {
            let ty = self.parse_ty()?;
            let lhs = self.read_value_id()?;
            self.expect_char(',')?;
            let rhs = self.read_value_id()?;
            return Ok(Inst::BinOp { op, ty, lhs, rhs });
        }

        // UnOp: "neg TY %a"
        if let Some(op) = Self::parse_unop(&opname) {
            let ty = self.parse_ty()?;
            let operand = self.read_value_id()?;
            return Ok(Inst::UnOp { op, ty, operand });
        }

        // CastOp: "sext TY %a to TY"
        if let Some(op) = Self::parse_castop(&opname) {
            let src_ty = self.parse_ty()?;
            let operand = self.read_value_id()?;
            self.expect_str("to")?;
            let dst_ty = self.parse_ty()?;
            return Ok(Inst::Cast {
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
    fn parse_dialect_op(&mut self) -> Result<Inst, ParseError> {
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
            self.advance(1);
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
        Ok(Inst::DialectOp(Box::new(inst)))
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
                    self.advance(1);
                }
                while let Some(ch) = self.peek_char() {
                    if ch.is_ascii_digit() {
                        self.advance(1);
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
                let len = self.read_u64()? as usize;
                self.expect_char(':')?;
                let start = self.pos;
                let hex_len = len * 2;
                if self.remaining().len() < hex_len {
                    return Err(self.error(format!(
                        "expected {} hex chars for bytes attr, got {}",
                        hex_len,
                        self.remaining().len()
                    )));
                }
                let hex = &self.input[start..start + hex_len];
                let mut bytes = Vec::with_capacity(len);
                for i in 0..len {
                    let pair = &hex[i * 2..i * 2 + 2];
                    let b = u8::from_str_radix(pair, 16)
                        .map_err(|_| self.error(format!("invalid hex byte '{}'", pair)))?;
                    bytes.push(b);
                }
                self.advance(hex_len);
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
    fn parse_instr_node(&mut self) -> Result<InstrNode, ParseError> {
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

        let mut node = InstrNode::new(inst);
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
    fn parse_block(&mut self) -> Result<Block, ParseError> {
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

        let mut block = Block::new(id);
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
    fn parse_function(&mut self) -> Result<(Function, FuncTyId), ParseError> {
        self.skip_whitespace();
        // Parse optional linkage and calling convention before 'fn'
        let linkage = self.try_parse_linkage();
        let calling_conv = self.try_parse_calling_conv();
        self.expect_str("fn")?;
        self.expect_char('@')?;
        // Read function name (alphanumeric + underscores)
        let name = self.read_ident()?;
        self.expect_char('(')?;
        self.expect_str("functy.")?;
        let ft_idx = self.read_u32()?;
        self.expect_char(')')?;
        self.expect_char('{')?;

        let ft_id = FuncTyId::new(ft_idx);
        // We need a FuncId but we'll set it later
        let mut func = Function::new(FuncId::new(0), name, ft_id, BlockId::new(0));
        func.linkage = linkage;
        func.calling_conv = calling_conv;

        // Function-level proof annotations and attributes (finding B). These
        // are `;`-comment lines emitted between `fn ... {` and the first block.
        // Parse any number of them, in any order, before the blocks.
        loop {
            self.skip_whitespace();
            if !self.remaining().starts_with("; #") {
                break;
            }
            // Consume the leading "; ".
            self.try_str(";");
            self.skip_whitespace_no_newline();
            if self.try_str("#proof:") {
                func.proofs.push(self.parse_proof_annotation()?);
                while self.try_str(",") {
                    func.proofs.push(self.parse_proof_annotation()?);
                }
            } else if self.try_str("#attrs:") {
                self.parse_func_attr_flags(&mut func.attrs)?;
            } else if self.try_str("#param_attrs") {
                self.parse_param_attrs(&mut func.attrs)?;
            } else if self.try_str("#producer:") {
                func.producer = Some(self.parse_producer()?);
            } else if self.try_str("#names:") {
                func.value_names = Some(self.parse_value_names()?);
            } else if self.try_str("#scope:") {
                let (index, scope) = self.parse_scope_data()?;
                let scopes = func.scopes.get_or_insert_with(Vec::new);
                if index as usize != scopes.len() {
                    return Err(self.error(format!(
                        "function scope entry {index} out of order (expected {})",
                        scopes.len()
                    )));
                }
                scopes.push(scope);
            } else if self.try_str("#source-provenance:") {
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
            } else if self.try_str("#source-loop:") {
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
            } else if self.try_str("#source-binding:") {
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
                // Unknown `; #...` directive: skip the rest of the line.
                self.skip_line();
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
            self.advance(1);
            let name = self.read_quoted_string()?;
            names.push((value, name));

            self.skip_whitespace_no_newline();
            match self.peek_char() {
                Some(',') => self.advance(1),
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
            self.advance("root".len());
            None
        } else if self.remaining().starts_with("parent=") {
            self.advance("parent=".len());
            Some(self.read_u32()?)
        } else {
            return Err(self.error("expected 'root' or 'parent=<index>' in #scope directive"));
        };

        self.skip_whitespace_no_newline();
        let span = if self.remaining().starts_with("at") {
            self.advance("at".len());
            Some(self.parse_loc_clause()?)
        } else {
            None
        };
        self.skip_whitespace_no_newline();
        if self.peek_char().is_some_and(|c| c != '\n') {
            return Err(self.error("unexpected trailing text in #scope directive"));
        }
        Ok((index, ScopeData { parent, span }))
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
                self.advance(tok.len());
                return Ok(producer);
            }
        }
        Err(self
            .error("expected producer token (trust, clean, trust-ir, tswift, tc) or quoted string"))
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
                other => return Err(self.error(format!("unknown param attr: '{}'", other))),
            }
        }
        if attrs.params.len() <= idx {
            attrs.params.resize(idx + 1, crate::ParamAttrs::default());
        }
        attrs.params[idx] = pa;
        Ok(())
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
    fn parse_struct_def(&mut self) -> Result<StructDef, ParseError> {
        self.expect_str("struct")?;
        self.expect_char('@')?;
        let name = self.read_ident()?;
        self.expect_char('{')?;

        let mut fields = Vec::new();
        self.skip_whitespace();
        if !self.remaining().starts_with('}') {
            let ty = self.parse_ty()?;
            fields.push(FieldDef {
                name: String::new(),
                ty,
                offset: None,
            });
            while self.try_str(",") {
                self.skip_whitespace();
                if self.remaining().starts_with('}') {
                    break;
                }
                let ty = self.parse_ty()?;
                fields.push(FieldDef {
                    name: String::new(),
                    ty,
                    offset: None,
                });
            }
        }
        self.expect_char('}')?;

        let mut size = None;
        let mut align = None;
        // Optional size=N and align=N
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("size=") {
            self.advance(5);
            size = Some(self.read_u64()?);
        }
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("align=") {
            self.advance(6);
            align = Some(self.read_u64()?);
        }
        // Optional ABI repr (`repr=c` / `repr=transparent` / `repr=packed(N)`);
        // absent means the default Rust repr.
        let mut repr = crate::ty::StructRepr::Rust;
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("repr=") {
            self.advance(5);
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
        })
    }

    /// Parse the trailing `id=N` clause emitted after struct/enum/record
    /// definitions (finding E). Defaults to the current table length when
    /// absent (back-compat with id-less text): the caller appends in order, so
    /// the table length is the positional id.
    fn parse_struct_kind_id_trailer(&mut self) -> Result<u32, ParseError> {
        self.skip_whitespace_no_newline();
        if self.remaining().starts_with("id=") {
            self.advance(3);
            self.read_u32()
        } else {
            // No explicit id: signal "use positional" via u32::MAX sentinel is
            // brittle; instead error so the writer/reader stay in lockstep. The
            // writer always emits an id, so reaching here means malformed text.
            Err(self.error("expected 'id=N' trailer on type definition"))
        }
    }

    /// Parse an enum definition:
    /// `enum @Name [repr(u8)] { Variant1 [= N], Variant2(TY, TY) [= N], ... } id=N`
    ///
    /// The optional `repr(..)` hint and per-variant `= N` explicit
    /// discriminants mirror `Display for Module`; when absent the historical
    /// all-implicit form parses to an empty `discriminants` vector (the
    /// canonical trimmed form: trailing implicit entries are not stored).
    fn parse_enum_def(&mut self) -> Result<EnumDef, ParseError> {
        self.expect_str("enum")?;
        self.expect_char('@')?;
        let name = self.read_ident()?;
        self.skip_whitespace();
        let mut repr = None;
        if self.try_str("repr") {
            self.expect_char('(')?;
            self.skip_whitespace();
            let width = self.read_ident()?;
            repr = Some(match width.as_str() {
                "u8" => crate::ty::EnumTagRepr::U8,
                "u16" => crate::ty::EnumTagRepr::U16,
                "u32" => crate::ty::EnumTagRepr::U32,
                "u64" => crate::ty::EnumTagRepr::U64,
                "i8" => crate::ty::EnumTagRepr::I8,
                "i16" => crate::ty::EnumTagRepr::I16,
                "i32" => crate::ty::EnumTagRepr::I32,
                "i64" => crate::ty::EnumTagRepr::I64,
                other => {
                    return Err(self.error(format!("invalid enum tag repr: '{other}'")));
                }
            });
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
                let variant_name = self.read_ident()?;
                let mut fields = Vec::new();
                if self.try_str("(") && !self.try_str(")") {
                    fields.push(self.parse_ty()?);
                    while self.try_str(",") {
                        self.skip_whitespace();
                        // Check if next is ')' (trailing comma)
                        if self.remaining().starts_with(')') {
                            break;
                        }
                        fields.push(self.parse_ty()?);
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
                    field_names: Vec::new(),
                });
                if !self.try_str(",") {
                    break;
                }
            }
        }
        self.expect_char('}')?;
        let id = self.parse_struct_kind_id_trailer()?;

        Ok(EnumDef {
            id: EnumId::new(id),
            name,
            variants,
            discriminants,
            repr,
            // The text format remains layout-agnostic. Concrete enum layouts
            // are carried by the versioned binary and serde formats.
            layout: None,
        })
    }

    /// Parse a record definition: record @Name { field: TY, field: TY } id=N
    fn parse_record_def(&mut self) -> Result<crate::ty::RecordDef, ParseError> {
        self.expect_str("record")?;
        self.expect_char('@')?;
        let name = self.read_ident()?;
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
                let field_name = self.read_ident()?;
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

    fn parse_ty_list(&mut self) -> Result<Vec<Ty>, ParseError> {
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

    fn parse_func_ty_params(&mut self) -> Result<(Vec<Ty>, bool), ParseError> {
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
                self.advance(3);
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
            self.advance(1);
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
            self.advance(3);
            let lo = self.read_i128()?;
            self.expect_char(',')?;
            let hi = self.read_i128()?;
            self.expect_char(']')?;
            Pred::Interval { lo, hi }
        } else if rem.starts_with("in{") {
            self.advance(3);
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
            self.advance(12);
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
            self.advance(if conj { 4 } else { 3 });
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

    fn parse_type_def(&mut self) -> Result<(u32, Ty), ParseError> {
        self.expect_str("type")?;
        self.expect_str("ty.")?;
        let id = self.read_u32()?;
        self.expect_char('=')?;
        let ty = self.parse_ty()?;
        Ok((id, ty))
    }

    /// Parse a function type definition: functy.N = (PARAMS...) -> (RETURNS...)
    fn parse_func_ty_def(&mut self) -> Result<(FuncTyId, FuncTy), ParseError> {
        self.expect_str("functy.")?;
        let id = FuncTyId::new(self.read_u32()?);
        self.expect_char('=')?;
        let (params, is_vararg) = self.parse_func_ty_params()?;
        self.expect_str("->")?;
        let returns = self.parse_ty_list()?;
        Ok((
            id,
            FuncTy {
                params,
                returns,
                is_vararg,
            },
        ))
    }

    /// Parse a global variable:
    /// global [linkage] [tls(model)] [mut] [align(N)] @Name TY [= VALUE]
    fn parse_global(&mut self) -> Result<Global, ParseError> {
        self.expect_str("global")?;
        let linkage = self.try_parse_linkage();
        let tls = self.try_parse_tls_model()?;
        let mutable = self.try_str("mut");
        let align = self.try_parse_global_align()?;
        self.expect_char('@')?;
        let name = self.read_ident()?;
        let ty = self.parse_ty()?;
        let initializer = if self.try_str("=") {
            Some(self.parse_constant()?)
        } else {
            None
        };
        Ok(Global {
            name,
            ty,
            mutable,
            initializer,
            linkage,
            tls,
            align,
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
            other => Err(self.error(format!("unknown obligation kind: '{}'", other))),
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
        let formula = if self.consume_keyword("formula") {
            let schema = self.read_quoted_string()?;
            let payload = self.read_quoted_string()?;
            let smtlib = if self.consume_keyword("smtlib") {
                Some(self.read_quoted_string()?)
            } else {
                None
            };
            let sort = if self.consume_keyword("sort") {
                Some(self.read_quoted_string()?)
            } else {
                None
            };
            Some(ProofFormula {
                schema,
                payload,
                smtlib,
                sort,
            })
        } else {
            None
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
                let algorithm = match self.read_quoted_string()?.as_str() {
                    "sha256" => ProofDigestAlgorithm::Sha256,
                    "trust_ir-stable-v1" => ProofDigestAlgorithm::TrustIrStableV1,
                    other => {
                        return Err(
                            self.error(format!("unknown proof digest algorithm: '{}'", other))
                        );
                    }
                };
                let bytes = self.parse_hash_array()?;
                Some(PublicObligationIdentity {
                    obligation_id,
                    semantic_digest: ProofDigest { algorithm, bytes },
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
        Ok(ProofObligation {
            id: ProofId::new(id),
            kind,
            status,
            description,
            formula,
            function,
            source,
            site,
        })
    }

    /// Read a u8 integer.
    fn read_u8(&mut self) -> Result<u8, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_digit() {
                self.advance(1);
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
                Ok(ProofEvidence::InheritedFromCallee {
                    callee: FuncId::new(callee),
                    obligation: ProofId::new(obligation),
                })
            }
            "clean_cic" => {
                let term = self.parse_byte_array()?;
                let context = self.parse_byte_array()?;
                let algorithm_name = self.read_quoted_string()?;
                let bytes = self.parse_hash_array()?;
                let algorithm = match algorithm_name.as_str() {
                    "sha256" => ProofDigestAlgorithm::Sha256,
                    "trust_ir-stable-v1" => ProofDigestAlgorithm::TrustIrStableV1,
                    other => {
                        return Err(
                            self.error(format!("unknown proof digest algorithm: '{}'", other))
                        );
                    }
                };
                Ok(ProofEvidence::CleanCic {
                    term,
                    context,
                    lineage: ProofDigest { algorithm, bytes },
                    // The textual format does not carry the kernel re-check
                    // directive; it travels in the serde/binary format.
                    kernel_recheck: None,
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
        Ok(ProofCertificate {
            obligation: ProofId::new(obligation_id),
            prover,
            evidence,
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
            self.advance(3);
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
            self.advance(7);
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
                self.advance(1);
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
                sm.vars.push(SpecVar {
                    name: vname,
                    ty: vty,
                });
            } else if self.consume_keyword("action") {
                sm.actions.push(self.read_quoted_string()?);
            } else if self.consume_keyword("invariant") {
                let iname = self.read_quoted_string()?;
                self.expect_char(':')?;
                let formula = self.read_quoted_string()?;
                sm.invariants.push(SpecInvariant {
                    name: iname,
                    formula,
                });
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

    // Skip header comments (the version header plus any further `;` lines
    // a producer emits before the `module` line).
    p.skip_whitespace();
    while p.remaining().starts_with(';') {
        p.skip_line();
        p.skip_whitespace();
    }

    // module "name"
    p.expect_str("module")?;
    let name = p.read_quoted_string()?;
    let mut module = Module::new(name);

    // Optional: target "triple" pointer_size endianness
    //           [abi="<id>"] [structpass=<policy>]
    p.skip_whitespace();
    if p.remaining().starts_with("target ") {
        p.advance(7); // "target "
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
                p.advance(4);
                abi = Some(p.read_quoted_string()?);
            } else if p.remaining().starts_with("structpass=") {
                p.advance(11);
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
    let mut func_idx = 0u32;

    // Helper: keywords that can start a function definition (linkage or cc prefixes)
    fn is_func_prefix(s: &str) -> bool {
        s.starts_with("fn ")
            || s.starts_with("internal ")
            || s.starts_with("private ")
            || s.starts_with("weak ")
            || s.starts_with("linkonce ")
            || s.starts_with("external ")
            || s.starts_with("fastcc ")
            || s.starts_with("coldcc ")
            || s.starts_with("rustcc ")
            || s.starts_with("swiftcc ")
            || s.starts_with("ccc ")
    }

    loop {
        p.skip_whitespace();
        if p.is_eof() {
            break;
        }
        let rem = p.remaining();

        // Skip comment lines
        if rem.starts_with(';') {
            p.skip_line();
            continue;
        }

        // Debug-info source-file table entries: `file N "path"`, emitted in
        // index order by Display.
        if rem.starts_with("file ") {
            p.advance(5);
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
            module.add_struct(sd);
        } else if rem.starts_with("enum ") {
            let ed = p.parse_enum_def()?;
            module.add_enum(ed);
        } else if rem.starts_with("record ") {
            let rd = p.parse_record_def()?;
            module.add_record(rd);
        } else if rem.starts_with("univ univ.") {
            let (id, universe) = p.parse_universe_def()?;
            let expected = module.universes.len() as u32;
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
            let expected = module.predicates.len() as u32;
            if id != expected {
                return Err(p.error(format!(
                    "non-contiguous predicate id: expected pred.{expected}, got pred.{id}"
                )));
            }
            module.predicates.push(pred);
        } else if rem.starts_with("type ty.") {
            // Module `types` table entry (finding A): `type ty.N = <Ty>`.
            let (id, ty) = p.parse_type_def()?;
            let expected = module.types.len() as u32;
            if id != expected {
                return Err(p.error(format!(
                    "non-contiguous type id: expected ty.{expected}, got ty.{id}"
                )));
            }
            module.add_type(ty);
        } else if rem.starts_with("functy.") {
            let (id, ft) = p.parse_func_ty_def()?;
            let expected = module.func_types.len() as u32;
            if id.index() != expected {
                return Err(p.error(format!(
                    "non-contiguous function type id: expected functy.{expected}, got functy.{}",
                    id.index()
                )));
            }
            module.add_func_type(ft);
        } else if rem.starts_with("closure_ty ") {
            let ct = p.parse_closure_ty_def()?;
            module.add_closure_type(ct);
        } else if rem.starts_with("global ") || rem.starts_with("global\t") {
            let g = p.parse_global()?;
            module.globals.push(g);
        } else if is_func_prefix(rem) {
            let (mut func, _ft_id) = p.parse_function()?;
            func.id = FuncId::new(func_idx);
            func_idx += 1;
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
            // Skip unknown lines
            p.skip_line();
        }
    }

    if let Err(errors) = module.validate_vector_select_contracts() {
        return Err(p.error(format!("{}", errors[0])));
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
mod tests {
    use super::*;
    use crate::constant::Constant;
    use crate::inst::{
        BinOp, CastOp, FCmpOp, ICmpOp, Inst, Ordering, OverflowOp, SwitchCase, UnOp,
    };
    use crate::node::InstrNode;
    use crate::ty::{FieldDef, FuncTy, StructDef, Ty};
    use crate::value::{BlockId, FuncId, StructId, ValueId};
    use crate::{Block, Function, Module};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
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
        let ft_id = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

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
        module.add_function(func);
        module
    }

    #[test]
    fn round_trip_add_module() {
        round_trip(&build_add_module());
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
        let ft_id = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_ctpop_module() {
        let mut module = Module::new("ctpop_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        module.add_function(func);
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
        let ft0 = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::Ptr],
            returns: vec![Ty::I64, Ty::Bool],
            is_vararg: false,
        });
        module.add_func_type(FuncTy {
            params: vec![Ty::Func(ft0), Ty::I8],
            returns: vec![],
            is_vararg: true,
        });

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
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_load_store() {
        let mut module = Module::new("mem");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_branches() {
        let mut module = Module::new("branches");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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

        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_cast() {
        let mut module = Module::new("cast_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_f16_float_surface() {
        let mut module = Module::new("f16_surface");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::F16, Ty::F32, Ty::I16],
            returns: vec![Ty::F16],
            is_vararg: false,
        });
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
        module.add_function(func);

        let text = format!("{}", module);
        assert!(text.contains("f16"));
        assert!(text.contains("fpext f16"));
        assert!(text.contains("fptrunc f32"));
        round_trip(&module);
    }

    #[test]
    fn round_trip_call() {
        let mut module = Module::new("call_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_icmp() {
        let mut module = Module::new("icmp_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_coro_suspend() {
        // A 2-state generator's yield point: load state, switch on it, and in
        // the yield arm `coro_suspend %frame, 0, 1, %yielded`.
        let mut module = Module::new("coro");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        module.add_function(func);
        // Structural-equality round-trip: catches any dropped field.
        round_trip_eq(&module);
    }

    #[test]
    fn round_trip_eh_opcodes() {
        // caller() invokes may_throw(); normal -> bb1, unwind -> bb2 (a
        // catch-all landing pad followed by resume). Exercises the text form
        // of all three EH opcodes.
        let mut module = Module::new("eh");
        let callee_ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let caller_ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        module.add_function(Function::new(FuncId::new(0), "may_throw", callee_ft, b(0)));

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
        module.add_function(func);
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
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_unreachable() {
        let mut module = Module::new("unr");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "panic", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_null_ptr() {
        let mut module = Module::new("null");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "get_null", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::NullPtr).with_result(v(0)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_alloca() {
        let mut module = Module::new("alloca_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_gep() {
        let mut module = Module::new("gep_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_switch() {
        let mut module = Module::new("switch");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_overflow() {
        let mut module = Module::new("overflow");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32, Ty::Bool],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_multiple_functions() {
        let mut module = Module::new("multi");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        for i in 0..3 {
            let mut func = Function::new(FuncId::new(i), format!("func_{i}"), ft, b(0));
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module.add_function(func);
        }
        round_trip(&module);
    }

    #[test]
    fn round_trip_atomics() {
        let mut module = Module::new("atomics");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_select() {
        let mut module = Module::new("select");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);
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
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_memory_role_and_parallel_annotations() {
        use crate::proof::{Divergence, ProofAnnotation};
        let mut module = Module::new("memory_role_and_parallel");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);
        round_trip(&module);
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
        });

        // Function
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

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
        });

        // Proof certificate
        module.proof_certificates.push(ProofCertificate {
            obligation: crate::value::ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::Trusted("manual review".to_string()),
        });

        round_trip(&module);
    }

    // --- New aggregate / closure types (issue #30) ---

    #[test]
    fn round_trip_set_type_bitset() {
        let mut module = Module::new("set_bitset");
        module.add_type(Ty::Set(TyId::new(0), SetRepr::Bitset));
        // A function that uses the type to pin it somewhere in text output
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Set(TyId::new(0), SetRepr::Bitset)],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .params
            .push((v(0), Ty::Set(TyId::new(0), SetRepr::Bitset)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_dialect_op() {
        use crate::dialect::{AttrValue, DialectInst};
        let mut module = Module::new("dialect_mod");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
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
        module.add_function(func);

        round_trip(&module);
    }

    #[test]
    fn round_trip_set_type_boxed() {
        let mut module = Module::new("set_boxed");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Set(TyId::new(0), SetRepr::Boxed)],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .params
            .push((v(0), Ty::Set(TyId::new(0), SetRepr::Boxed)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_sequence_type() {
        let mut module = Module::new("seq_ty");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Sequence(TyId::new(0))],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Sequence(TyId::new(0))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
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
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Record(RecordId::new(0))],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "take_rec", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Record(RecordId::new(0))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn round_trip_closure_def_and_type() {
        let mut module = Module::new("closures");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        module.add_closure_type(crate::ty::ClosureTy {
            func: ft,
            captures: vec![Ty::I32, Ty::Bool],
        });
        let user_ft = module.add_func_type(FuncTy {
            params: vec![Ty::Closure(ClosureTyId::new(0))],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "take_clos", user_ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Closure(ClosureTyId::new(0))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
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
        });
        round_trip(&module);
    }

    #[test]
    fn round_trip_dialect_op_no_results_no_attrs() {
        use crate::dialect::DialectInst;
        let mut module = Module::new("dialect_mod2");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

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
        let i32_id = m.add_type(Ty::I32); // ty.0
        let u8_id = m.add_type(Ty::U8); // ty.1
        let ft = m.add_func_type(FuncTy {
            params: vec![
                Ty::Array(i32_id, 4),
                Ty::Sequence(u8_id),
                Ty::Set(i32_id, crate::ty::SetRepr::Bitset),
            ],
            returns: vec![],
            is_vararg: false,
        });
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
        m.add_function(func);

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
        let ft = m.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        m.add_function(func);

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
        let ft = m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        for (i, producer) in producers.iter().enumerate() {
            let mut func = Function::new(FuncId::new(i as u32), format!("f{i}"), ft, b(0));
            func.producer = Some(producer.clone());
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            m.add_function(func);
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

    #[test]
    fn round_trip_semantic_source_provenance_directives() {
        let mut m = Module::new("source_provenance_text");
        let ft = m.add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![],
            is_vararg: false,
        });
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
        m.add_function(func);

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
        let ft = m.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
            },
            ScopeData {
                parent: Some(0),
                span: None,
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
        m.add_function(func);

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
        let ft = m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
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
        m.add_function(func);
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
        let ft = m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
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
        m.add_function(func);
        round_trip_eq(&m);
    }

    /// D: ValueRange / KnownBits / Wrapping / ProofRef all round-trip through text.
    #[test]
    fn round_trip_value_fact_proof_annotations() {
        let mut m = Module::new("value_facts");
        let ft = m.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        m.add_function(func);
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
        let ft = m.add_func_type(FuncTy {
            params: vec![
                Ty::Struct(StructId::new(5)),
                Ty::Enum(EnumId::new(9)),
                Ty::Record(RecordId::new(3)),
            ],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Struct(StructId::new(5))));
        block.params.push((v(1), Ty::Enum(EnumId::new(9))));
        block.params.push((v(2), Ty::Record(RecordId::new(3))));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        m.add_function(func);

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
        let ft = m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
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
        m.add_function(func);

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
            let ft = m.add_func_type(FuncTy {
                params: vec![param],
                returns: vec![],
                is_vararg: false,
            });
            m.add_function(Function::new(FuncId::new(0), "f", ft, b(0)));
            let text = format!("{}", m);
            parse_module(&text).unwrap().func_types[0].params[0].clone()
        };
        assert_eq!(round_trip(Ty::Unit), Ty::Unit);
        assert_eq!(round_trip(Ty::Tuple(Vec::new())), Ty::Tuple(Vec::new()));
        let _ = TyId::new(0); // keep TyId import used across cfg paths
    }
}
