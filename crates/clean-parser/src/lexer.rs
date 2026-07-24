// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lexer for Lean 4 syntax
//!
//! Tokenizes Lean source text into a stream of tokens.

use crate::surface::{DocComment, Span};
use clean_kernel::BigNat;
use std::iter::Peekable;
use std::str::CharIndices;

/// Kind of string interpolation prefix.
///
/// In Lean 4, interpolated strings use a prefix before `!"`:
/// - `s!"..."` — string interpolation
/// - `m!"..."` — message interpolation (for error messages)
/// - `f!"..."` — format interpolation (for formatted output)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum InterpolatedStringKind {
    String,
    MessageData,
    Format,
}

/// Token type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // Keywords
    Def,
    Theorem,
    Lemma,
    Axiom,
    Opaque, // opaque declaration (type known, implementation hidden)
    Example,
    Let,
    In,
    Fun,
    Forall,
    If,
    Then,
    Else,
    Match,
    With,
    Where,
    Do,
    Return,
    Structure,
    Class,
    Instance,
    Inductive,
    Coinductive, // Lean 4.25+ coinductive predicates (greatest fixpoint)
    Deriving,
    Namespace,
    Section,
    End,
    Open,
    Export,
    Variable,
    Universe,
    Import,
    Mutual,
    SetOption,
    By,
    Have,
    Show,
    Suffices,
    From,
    Rfl,
    Sorry,
    Extends,
    Private,
    Protected,
    Public, // Lean 4 module system: `public import`, `public section`, `public def`
    Module, // Lean 4 module system: leading `module` header command
    Partial,
    Unsafe,
    Noncomputable,
    Abbrev,
    Attribute,
    Syntax,     // syntax command for custom syntax
    Macro,      // macro command
    MacroRules, // macro_rules command (multi-arm macros)
    Elab,       // elab command for custom elaborators
    Infixl,     // left-associative infix notation
    Infixr,     // right-associative infix notation
    Infix,      // non-associative infix notation
    Prefix,     // prefix notation
    Postfix,    // postfix notation
    Notation,   // general notation command
    Scoped,     // scoped modifier
    Hiding,     // open ... hiding ...
    Renaming,   // open ... renaming ...
    Rec,        // rec keyword (for let rec)

    // Types
    Type,
    Prop,
    Sort,

    // Identifiers and literals
    Ident(String),
    /// Natural-number literal. Arbitrary-precision: Lean 4 `Nat` literals are
    /// unbounded, so the accumulator is a kernel `BigNat` rather than a `u64`.
    /// Values below `2^64` are stored as `BigNat::Small` (no heap); values at or
    /// above the `u64` boundary (`18446744073709551616`, `0xFFFF…FFFF + 1`, a
    /// 100-digit decimal, …) keep their exact value in a multi-limb `BigNat`.
    NatLit(BigNat),
    /// Floating-point literal: `3.14`, `1e-5`, `2.5E10`. Lean 4 elaborates
    /// these via `OfScientific`. Stored as normalized source text (underscores
    /// stripped) so the literal is represented losslessly rather than rounded
    /// through an `f64`.
    FloatLit(String),
    /// Character literal: `'a'`, `'\n'`, `'\u{1F600}'`. Lean 4 `Char`.
    CharLit(char),
    StringLit(String),
    /// Raw syntax quotation: `(foo $bar)` captured after a backtick
    SyntaxQuote(String),
    /// Interpolated string: `s!"hello {name}"`, `m!"..."`, `f!"..."`
    /// Contains the prefix kind and the raw string body (content between quotes).
    InterpolatedString(InterpolatedStringKind, String),

    // Delimiters
    LParen,        // (
    RParen,        // )
    LBrace,        // {
    RBrace,        // }
    LBracket,      // [
    RBracket,      // ]
    RBracketPrime, // ]' (GetElem proof-variant closer, `xs[i]'h`; one Lean token)
    LAngle,        // ⟨ (Unicode angle bracket for anonymous constructors)
    RAngle,        // ⟩ (Unicode angle bracket for anonymous constructors)
    LDAngle,       // ⟪ (Unicode double angle bracket - inner product)
    RDAngle,       // ⟫ (Unicode double angle bracket - inner product)
    LFrench,       // ‹ (U+2039) anonymous-hypothesis open (`‹P›` → `(P by assumption)`)
    RFrench,       // › (U+203A) anonymous-hypothesis close
    BackwardPipe,  // <| (backward/reverse pipe operator - low-precedence application)
    ForwardPipe,   // |> (forward pipe operator - `x |> f` = `f x`, `infixl`)

    // Punctuation
    Colon,      // :
    ColonColon, // :: (cons operator)
    ColonEq,    // :=
    Comma,      // ,
    Dot,        // .
    DotDot,     // .. (range operator)
    Semicolon,  // ;
    Arrow,      // → or ->
    FatArrow,   // =>
    Lambda,     // λ or fun
    Pi,         // Π or forall
    At,         // @
    Hash,       // #
    Question,   // ? (synthetic-hole prefix: `?_`, `?name`)
    Underscore, // _
    Pipe,       // |
    Turnstile,  // ⊢ or |-
    Amp,        // &
    AmpAmp,     // && (Bool.and, infixr:35)
    PipePipe,   // || (Bool.or, infixr:30)
    BitAnd,     // &&& (HAnd.hAnd, infixl:60)
    BitOr,      // ||| (HOr.hOr, infixl:55)
    BitXor,     // ^^^ (HXor.hXor, infixl:58)
    ShiftL,     // <<< (HShiftLeft.hShiftLeft, infixl:75)
    ShiftR,     // >>> (HShiftRight.hShiftRight, infixl:75)
    SlashSlash, // // (Subtype separator `{ x // p }`; one Lean token)
    Star,       // *
    Plus,       // +
    PlusPlus,   // ++ (HAppend.hAppend / String.append, infixl:65)
    Minus,      // -
    Slash,      // /
    Caret,      // ^ (exponentiation)
    Eq,         // =
    DoubleEq,   // == (BEq equality check)
    Ne,         // ≠ (propositional disequality, Ne)
    BNe,        // != (Boolean disequality, bne)
    Lt,         // <
    Le,         // ≤ or <=
    Gt,         // >
    Ge,         // ≥ or >=
    And,        // ∧ or /\
    Or,         // ∨ or \/
    Not,        // ¬ or !
    Tilde,      // ~ (user-defined operators)
    Percent,    // % (modulo operator)

    // Additional Unicode operators
    HEq,             // ≍ (heterogeneous equality)
    Equiv,           // ≃ (equivalence/isomorphism)
    Approx,          // ≈ (HasEquiv.Equiv — setoid/quotient equivalence)
    InvNotation,     // ⁻¹ (postfix Inv.inv — group/field inverse)
    Sup,             // ⊔ (Max.max — lattice join, syntax:68)
    Inf,             // ⊓ (Min.min — lattice meet, syntax:69)
    BigSup,          // ⨆ (iSup — indexed supremum big-operator, `⨆ i, f i`)
    BigInf,          // ⨅ (iInf — indexed infimum big-operator, `⨅ i, f i`)
    SetProd,         // ×ˢ (SProd.sprod — Set/Finset product, infixr:82)
    CatComp,         // ≫ (CategoryStruct.comp — morphism composition, infixr:80)
    HomArrow,        // ⟶ (Quiver.Hom — morphism type `a ⟶ b`, infixr:10)
    Iff,             // ↔
    Times,           // ×
    Oplus,           // ⊕ (Sum type)
    Sigma,           // Σ (Sigma dependent-pair type binder)
    LeftArrow,       // ←
    Exists,          // ∃
    ExistsUnique,    // ∃!
    Elem,            // ∈
    NotElem,         // ∉
    Subset,          // ⊆
    ProperSubset,    // ⊂
    SDiff,           // \
    Inter,           // ∩
    Union,           // ∪
    EmptySet,        // ∅
    Top,             // ⊤
    Bot,             // ⊥
    Compose,         // ∘
    Cdot,            // · (section placeholder / middle dot)
    Dollar,          // $ (low-precedence application)
    DollarArrow,     // $>
    LeftDollar,      // <$
    LeftDollarArrow, // <$>
    Bind,            // >>=
    Seq,             // >> (HAndThen.hAndThen, syntax:60, right)
    AndThen,         // *> (SeqRight.seqRight, syntax:60, left)
    SeqLeft,         // <* (SeqLeft.seqLeft, syntax:60, left)
    SeqAp,           // <*> (Seq.seq, syntax:60, left)
    MapRev,          // <&> (Functor.mapRev, infixr:100)
    BindLeft,        // =<< (Bind.bindLeft, infixr:55)
    KleisliR,        // >=> (Bind.kleisliRight, infixr:55)
    KleisliL,        // <=< (Bind.kleisliLeft, infixr:55)
    OrElse,          // <|>
    SeqFocusOp,      // <;> (tactic sequential focus combinator)
    Dvd,             // ∣ (Dvd.dvd, infix:50)
    Smul,            // • (HSMul.hSMul, infixr:73)
    Subst,           // ▸ (Term.subst / Eq.rec, trailing:75, right)
    StrictLBrace,    // ⦃ (strict-implicit binder open)
    StrictRBrace,    // ⦄ (strict-implicit binder close)
    PSigma,          // Σ' (PSigma dependent-pair binder)
    TimesPrime,      // ×' (anonymous PSigma constructor)

    // Big operators (Mathlib notation)
    BigSum,   // ∑ (Finset.sum / tsum)
    BigProd,  // ∏ (Finset.prod / tprod)
    Integral, // ∫ (MeasureTheory.integral)
    FintAvg,  // ⨍ (MeasureTheory.laverage / fint)
    BigUnion, // ⋃ (Set.iUnion / ⋃)
    BigInter, // ⋂ (Set.iInter / ⋂)

    // Special
    Eof,
    Error(LexError),
}

/// Typed lexer error — replaces the former `Error(String)` to enable
/// reliable pattern matching in grammar error-recovery paths.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum LexError {
    /// Character that is not part of any valid token.
    #[error("unexpected character: {0}")]
    UnexpectedChar(char),
    /// String literal missing its closing `"`.
    #[error("unterminated string")]
    UnterminatedString,
    /// Syntax quotation (backtick) missing its closing delimiter.
    #[error("unterminated syntax quote")]
    UnterminatedSyntaxQuote,
    /// Guillemet-quoted identifier `«...»` missing closing `»`.
    #[error("unterminated quoted identifier")]
    UnterminatedQuotedIdent,
    /// Guillemet-quoted identifier `«»` has no content.
    #[error("empty quoted identifier")]
    EmptyQuotedIdent,
    /// Backslash followed by an unrecognized character.
    #[error("unknown escape sequence: \\{0}")]
    UnknownEscapeSequence(char),
    /// Numeric literal exceeds `u64::MAX`.
    #[error("numeric literal overflows u64")]
    NumericOverflow,
    /// Character literal missing its closing `'`.
    #[error("unterminated character literal")]
    UnterminatedChar,
    /// Character literal does not contain exactly one character (`''` or `'ab'`).
    #[error("invalid character literal")]
    InvalidChar,
    /// `\u{...}` / `\x..` escape that does not denote a valid scalar value.
    #[error("invalid unicode escape sequence")]
    InvalidUnicodeEscape,
    /// A string gap (`\` followed by whitespace) that does not contain exactly
    /// one newline: either non-whitespace appeared before any newline
    /// (`expecting newline`) or a second newline appeared (`additional newline`).
    #[error("string gap must contain exactly one newline")]
    InvalidStringGap,
}

impl TokenKind {
    /// Construct a `NatLit` from a `u64` value (the common small-literal case).
    /// Kept as a convenience for callers and tests that build literals below the
    /// `u64` boundary without spelling out the `BigNat::Small` wrapper.
    #[must_use]
    pub fn nat_lit(n: u64) -> Self {
        TokenKind::NatLit(BigNat::Small(n))
    }

    /// Returns the keyword string if this is a keyword token.
    ///
    /// Used by the parser to accept keywords after a dot when parsing projections
    /// (e.g., `Nat.rec`, `Option.Type`). The elaborator later resolves projection
    /// chains to constants when needed.
    pub fn as_keyword_str(&self) -> Option<&'static str> {
        match self {
            TokenKind::Def => Some("def"),
            TokenKind::Theorem => Some("theorem"),
            TokenKind::Lemma => Some("lemma"),
            TokenKind::Axiom => Some("axiom"),
            TokenKind::Example => Some("example"),
            TokenKind::Let => Some("let"),
            TokenKind::In => Some("in"),
            TokenKind::Fun => Some("fun"),
            TokenKind::Forall => Some("forall"),
            TokenKind::If => Some("if"),
            TokenKind::Then => Some("then"),
            TokenKind::Else => Some("else"),
            TokenKind::Match => Some("match"),
            TokenKind::With => Some("with"),
            TokenKind::Where => Some("where"),
            TokenKind::Do => Some("do"),
            TokenKind::Return => Some("return"),
            TokenKind::Structure => Some("structure"),
            TokenKind::Class => Some("class"),
            TokenKind::Instance => Some("instance"),
            TokenKind::Inductive => Some("inductive"),
            TokenKind::Coinductive => Some("coinductive"),
            TokenKind::Deriving => Some("deriving"),
            TokenKind::Namespace => Some("namespace"),
            TokenKind::Section => Some("section"),
            TokenKind::End => Some("end"),
            TokenKind::Open => Some("open"),
            TokenKind::Variable => Some("variable"),
            TokenKind::Universe => Some("universe"),
            TokenKind::Import => Some("import"),
            TokenKind::Mutual => Some("mutual"),
            TokenKind::SetOption => Some("set_option"),
            TokenKind::By => Some("by"),
            TokenKind::Have => Some("have"),
            TokenKind::Show => Some("show"),
            TokenKind::Suffices => Some("suffices"),
            TokenKind::From => Some("from"),
            TokenKind::Rfl => Some("rfl"),
            TokenKind::Sorry => Some("sorry"),
            TokenKind::Extends => Some("extends"),
            TokenKind::Private => Some("private"),
            TokenKind::Protected => Some("protected"),
            TokenKind::Public => Some("public"),
            TokenKind::Module => Some("module"),
            TokenKind::Partial => Some("partial"),
            TokenKind::Unsafe => Some("unsafe"),
            TokenKind::Noncomputable => Some("noncomputable"),
            TokenKind::Abbrev => Some("abbrev"),
            TokenKind::Attribute => Some("attribute"),
            TokenKind::Syntax => Some("syntax"),
            TokenKind::Macro => Some("macro"),
            TokenKind::MacroRules => Some("macro_rules"),
            TokenKind::Elab => Some("elab"),
            TokenKind::Infixl => Some("infixl"),
            TokenKind::Infixr => Some("infixr"),
            TokenKind::Infix => Some("infix"),
            TokenKind::Prefix => Some("prefix"),
            TokenKind::Postfix => Some("postfix"),
            TokenKind::Notation => Some("notation"),
            TokenKind::Scoped => Some("scoped"),
            TokenKind::Hiding => Some("hiding"),
            TokenKind::Renaming => Some("renaming"),
            TokenKind::Rec => Some("rec"),
            TokenKind::Type => Some("Type"),
            TokenKind::Prop => Some("Prop"),
            TokenKind::Sort => Some("Sort"),
            _ => None,
        }
    }
}

/// A token with its span
#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// Whether this token is preceded by a newline in the original source.
    ///
    /// Used for limited layout-sensitive parsing (e.g., disambiguating `let` bodies).
    pub preceded_by_newline: bool,
    /// Column at token start: 0-based byte offset from the last newline (or start of input).
    /// Matches Lean 4's byte-offset column model.
    pub col: u32,
    /// 1-based line number at token start.
    pub line: u32,
}

impl Token {
    /// Create a new token with the given kind, span, newline flag, column, and line.
    ///
    /// # ENSURES
    /// - Returns Token with fields set to provided values
    #[must_use]
    pub fn new(
        kind: TokenKind,
        span: Span,
        preceded_by_newline: bool,
        col: u32,
        line: u32,
    ) -> Self {
        Self {
            kind,
            span,
            preceded_by_newline,
            col,
            line,
        }
    }

    /// Create an EOF token at the given position.
    ///
    /// # ENSURES
    /// - Returns Token with `kind == TokenKind::Eof`
    /// - `span.start == span.end == pos` (zero-width span)
    #[must_use]
    pub fn eof(pos: usize, preceded_by_newline: bool, col: u32, line: u32) -> Self {
        Self {
            kind: TokenKind::Eof,
            span: Span::new(pos, pos),
            preceded_by_newline,
            col,
            line,
        }
    }
}

/// Lexer state
///
/// Tokenizes Lean 4 source text into a stream of tokens.
/// Handles Unicode operators, nested block comments, and line comments.
pub struct Lexer<'a> {
    chars: Peekable<CharIndices<'a>>,
    pos: usize,
    /// Byte offset of the start of the current line (after the last `\n`).
    /// Used to compute column as `pos - line_start`.
    line_start: usize,
    /// 1-based line number, incremented on each `\n`.
    line: u32,
    /// The most recent character returned by `next_char` (including whitespace
    /// and comment characters). `None` at the start of input. Used to decide
    /// whether a `.<digit>` is a leading-dot float (`.5`) — only at a token
    /// boundary preceded by whitespace or start-of-input — versus a projection
    /// dot glued to a preceding token (`x.5`).
    prev_char: Option<char>,
    /// Lean declaration doc comments (`/-- ... -/`) encountered while skipping
    /// trivia, in source order. Captured here rather than emitted as tokens so
    /// the existing token stream is unchanged; the parser associates each doc
    /// with the declaration that immediately follows it. Module/section docs
    /// (`/-! ... -/`) and ordinary block comments (`/- ... -/`) are not
    /// recorded.
    doc_comments: Vec<DocComment>,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer for the given input.
    ///
    /// # ENSURES
    /// - `pos == 0` (lexer starts at beginning)
    /// - Ready to produce tokens via `next_token()`
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.char_indices().peekable(),
            pos: 0,
            line_start: 0,
            line: 1,
            prev_char: None,
            doc_comments: Vec::new(),
        }
    }

    /// Tokenize all input into a vector of tokens.
    ///
    /// # ENSURES
    /// - Returns non-empty vector (at minimum contains EOF token)
    /// - Last token is always `TokenKind::Eof`
    /// - All token spans are within `0..input.len()`
    /// - Token sequence is deterministic for same input
    #[must_use]
    pub fn tokenize(input: &str) -> Vec<Token> {
        Self::tokenize_with_docs(input).0
    }

    /// Tokenize all input, also returning any declaration doc comments
    /// (`/-- ... -/`) encountered, in source order.
    ///
    /// The token vector is identical to [`Lexer::tokenize`] — doc comments are
    /// skipped as trivia, not emitted as tokens. They are returned as a
    /// side-channel so callers (e.g. the parser) can associate each doc with
    /// the declaration that follows it.
    ///
    /// # ENSURES
    /// - Token vector matches `tokenize(input)` exactly
    /// - Doc comments are in source order with spans within `0..input.len()`
    #[must_use]
    pub fn tokenize_with_docs(input: &str) -> (Vec<Token>, Vec<DocComment>) {
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();
        loop {
            let tok = lexer.next_token();
            let is_eof = tok.kind == TokenKind::Eof;
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        (tokens, lexer.doc_comments)
    }

    fn peek_char(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    fn next_char(&mut self) -> Option<(usize, char)> {
        let result = self.chars.next();
        if let Some((i, c)) = result {
            self.pos = i + c.len_utf8();
            self.prev_char = Some(c);
        }
        result
    }

    fn skip_whitespace(&mut self) -> bool {
        let mut saw_newline = false;
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() {
                if c == '\n' {
                    saw_newline = true;
                }
                self.next_char();
                if c == '\n' {
                    // Record line start as position AFTER the newline
                    self.line_start = self.pos;
                    self.line += 1;
                }
            } else if c == '-' {
                // Check for line comment --
                let start = self.pos;
                let saved_chars = self.chars.clone();
                let saved_line_start = self.line_start;
                let saved_prev_char = self.prev_char;
                self.next_char();
                if self.peek_char() == Some('-') {
                    // Line comment, skip to end of line
                    while let Some(c) = self.peek_char() {
                        self.next_char();
                        if c == '\n' {
                            saw_newline = true;
                            self.line_start = self.pos;
                            self.line += 1;
                            break;
                        }
                    }
                } else {
                    // Not a comment, restore
                    self.chars = saved_chars;
                    self.pos = start;
                    self.line_start = saved_line_start;
                    self.prev_char = saved_prev_char;
                    break;
                }
            } else if c == '/' {
                // Check for block comment /-
                let start = self.pos;
                let saved_chars = self.chars.clone();
                let saved_line_start = self.line_start;
                let saved_prev_char = self.prev_char;
                self.next_char();
                if self.peek_char() == Some('-') {
                    self.next_char();
                    // We have consumed `/-`. A third `-` makes this a Lean
                    // declaration doc comment `/-- ... -/`; a `!` makes it a
                    // module/section doc `/-! ... -/` (not captured here);
                    // anything else is an ordinary block comment.
                    //
                    // Guard against `/--/` (an unterminated/empty comment whose
                    // third char is part of the would-be closer): only treat as
                    // a doc comment when the char after `/--` is not `/`.
                    let is_doc = self.peek_char() == Some('-') && {
                        // Peek the character that would follow the third `-`
                        // (the fourth char overall). `nth(1)` on a clone of the
                        // iterator yields it without consuming.
                        self.chars.clone().nth(1).map(|(_, c)| c) != Some('/')
                    };
                    if is_doc {
                        // Consume the third `-` of the `/--` opener.
                        self.next_char();
                        // Block doc comment, skip to -/ while capturing the
                        // inner text. `depth` tracks nested `/- -/` pairs.
                        let mut depth = 1;
                        let mut text = String::new();
                        while depth > 0 {
                            match self.next_char() {
                                Some((_, '\n')) => {
                                    saw_newline = true;
                                    self.line_start = self.pos;
                                    self.line += 1;
                                    text.push('\n');
                                }
                                Some((_, '/')) if self.peek_char() == Some('-') => {
                                    self.next_char();
                                    depth += 1;
                                    text.push('/');
                                    text.push('-');
                                }
                                Some((_, '-')) if self.peek_char() == Some('/') => {
                                    self.next_char();
                                    depth -= 1;
                                    if depth > 0 {
                                        text.push('-');
                                        text.push('/');
                                    }
                                }
                                Some((_, ch)) => text.push(ch),
                                None => break,
                            }
                        }
                        self.doc_comments.push(DocComment::new(
                            Span::new(start, self.pos),
                            text.trim().to_string(),
                        ));
                    } else {
                        // Block comment, skip to -/
                        let mut depth = 1;
                        while depth > 0 {
                            match self.next_char() {
                                Some((_, '\n')) => {
                                    saw_newline = true;
                                    self.line_start = self.pos;
                                    self.line += 1;
                                }
                                Some((_, '/')) if self.peek_char() == Some('-') => {
                                    self.next_char();
                                    depth += 1;
                                }
                                Some((_, '-')) if self.peek_char() == Some('/') => {
                                    self.next_char();
                                    depth -= 1;
                                }
                                None => break,
                                _ => {}
                            }
                        }
                    }
                } else {
                    // Not a comment, restore
                    self.chars = saved_chars;
                    self.pos = start;
                    self.line_start = saved_line_start;
                    self.prev_char = saved_prev_char;
                    break;
                }
            } else {
                break;
            }
        }

        saw_newline
    }

    pub fn next_token(&mut self) -> Token {
        let preceded_by_newline = self.skip_whitespace();

        let start = self.pos;
        let col = (start - self.line_start) as u32;
        let line = self.line;

        // The character immediately preceding this token (after any whitespace
        // and comments were skipped). `None` at start-of-input, and whitespace
        // when the token follows a space/newline. Captured before consuming the
        // first character so the `.` arm can distinguish a leading-dot float
        // (`.5`, at a token boundary) from a projection dot (`x.5`).
        let preceding_char = self.prev_char;

        let Some((_, c)) = self.next_char() else {
            return Token::eof(start, preceded_by_newline, col, line);
        };

        let kind = match c {
            // Single-character tokens
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => {
                // `]'` is a single Lean token (the GetElem proof-variant closer,
                // `xs[i]'h`). It only forms when `'` is byte-adjacent to `]`;
                // `xs[1] 'h'` (space) stays `]` + a char literal.
                if self.peek_char() == Some('\'') {
                    self.next_char();
                    TokenKind::RBracketPrime
                } else {
                    TokenKind::RBracket
                }
            }
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            '@' => TokenKind::At,
            '#' => TokenKind::Hash,
            // `?` is the synthetic-hole prefix (Lean 4 `?_`, `?name`). The
            // parser combines it with an immediately-following `_`/identifier
            // into a single synthetic hole; a bare `?` is also a hole. Lexing
            // it as a real token (rather than `Error(UnexpectedChar('?'))`)
            // prevents `?_` from being glued into a spurious `App(Hole, Hole)`.
            '?' => TokenKind::Question,
            '`' => self.lex_backtick(start),
            '«' => self.lex_guillemet_ident(),
            '_' => {
                // Could be underscore or start of identifier
                // Use is_ident_continue to properly handle _' _? _! etc.
                if self.peek_char().is_some_and(is_ident_continue) {
                    self.lex_ident(start, c)
                } else {
                    TokenKind::Underscore
                }
            }
            '|' => {
                if self.peek_char() == Some('>') {
                    self.next_char();
                    // `|>` is the forward pipe operator (`x |> f` = `f x`,
                    // `x |>.foo` = `x.foo`). It is a dedicated token — NOT the
                    // closing angle bracket `⟩` — so the parser can desugar
                    // pipelines. (A previous version lexed `|>` as `RAngle`,
                    // conflating it with anonymous-constructor close and making
                    // `n |> f` a parse error.)
                    TokenKind::ForwardPipe
                } else if self.peek_char() == Some('-') {
                    self.next_char();
                    TokenKind::Turnstile
                } else if self.peek_char() == Some('|') {
                    self.next_char();
                    if self.peek_char() == Some('|') {
                        self.next_char();
                        TokenKind::BitOr // |||  (HOr.hOr)
                    } else {
                        TokenKind::PipePipe // ||  (Bool.or)
                    }
                } else {
                    TokenKind::Pipe
                }
            }
            '&' => {
                if self.peek_char() == Some('&') {
                    self.next_char();
                    if self.peek_char() == Some('&') {
                        self.next_char();
                        TokenKind::BitAnd // &&&  (HAnd.hAnd)
                    } else {
                        TokenKind::AmpAmp // &&  (Bool.and)
                    }
                } else {
                    TokenKind::Amp
                }
            }
            '*' => {
                if self.peek_char() == Some('>') {
                    self.next_char();
                    TokenKind::AndThen
                } else {
                    TokenKind::Star
                }
            }
            '+' => {
                // `++` is the append operator (HAppend.hAppend / String.append,
                // infixl:65). A bare `+` stays addition (HAdd.hAdd). Without this
                // the lexer split `++` into `Plus, Plus`, parsing `a ++ b` as
                // `HAdd.hAdd a b` (with a no-op prefix `+`), which has no String
                // instance and leaked a fresh metavariable into the elaborated
                // body ("contains free variables").
                if self.peek_char() == Some('+') {
                    self.next_char();
                    TokenKind::PlusPlus
                } else {
                    TokenKind::Plus
                }
            }
            '^' => {
                // `^^^` is the bitwise-xor operator (HXor.hXor). A bare `^` stays
                // exponentiation; `^^` is not a Lean operator so we only collapse
                // the full three-caret sequence.
                if self.peek_char() == Some('^') {
                    let saved_chars = self.chars.clone();
                    let saved_pos = self.pos;
                    self.next_char();
                    if self.peek_char() == Some('^') {
                        self.next_char();
                        TokenKind::BitXor // ^^^  (HXor.hXor)
                    } else {
                        // Not `^^^`; backtrack to a single `^`.
                        self.chars = saved_chars;
                        self.pos = saved_pos;
                        TokenKind::Caret
                    }
                } else {
                    TokenKind::Caret
                }
            }
            '$' => {
                if self.peek_char() == Some('>') {
                    self.next_char();
                    TokenKind::DollarArrow
                } else {
                    TokenKind::Dollar
                }
            }

            // Multi-character tokens
            ':' => {
                if self.peek_char() == Some('=') {
                    self.next_char();
                    TokenKind::ColonEq
                } else if self.peek_char() == Some(':') {
                    self.next_char();
                    TokenKind::ColonColon
                } else {
                    TokenKind::Colon
                }
            }
            '.' => {
                // Leading-dot float shorthand: `.5` is the float `0.5` in Lean 4.
                // This only fires at a genuine token boundary — when the `.` is
                // not glued to a preceding *expression* — and the next character
                // is an ASCII digit. A `.` immediately following an identifier /
                // number character or a closing delimiter (`x.5`, `(x).5`) stays
                // a projection dot; `..` (range) and a bare `.` operator are
                // handled below. `1.5`/`1..2` never reach here because
                // `lex_number` consumes the leading `.` itself.
                let at_token_boundary = preceding_char.is_none_or(starts_leading_dot_float);
                if at_token_boundary && self.peek_char().is_some_and(|c| c.is_ascii_digit()) {
                    self.lex_leading_dot_float()
                } else if self.peek_char() == Some('.') {
                    self.next_char();
                    TokenKind::DotDot
                } else {
                    TokenKind::Dot
                }
            }
            '=' => {
                if self.peek_char() == Some('>') {
                    self.next_char();
                    TokenKind::FatArrow
                } else if self.peek_char() == Some('=') {
                    self.next_char();
                    TokenKind::DoubleEq
                } else if self.peek_char() == Some('<') {
                    // `=<<` is Bind.bindLeft (infixr:55). A bare `=<` is not a Lean
                    // token, so require the full `=<<`; otherwise keep `<` for the
                    // next token and return `=` (Eq). Previously `=<<` lexed as
                    // `Eq` + the angle-cluster `Ident("<<")`, a silent misparse of
                    // `f =<< x` into `Eq f (App "<<" [x])` (audit RANK 22).
                    let saved_chars = self.chars.clone();
                    let saved_pos = self.pos;
                    self.next_char(); // consume first '<'
                    if self.peek_char() == Some('<') {
                        self.next_char();
                        TokenKind::BindLeft
                    } else {
                        self.chars = saved_chars;
                        self.pos = saved_pos;
                        TokenKind::Eq
                    }
                } else {
                    TokenKind::Eq
                }
            }
            '-' => {
                if self.peek_char() == Some('>') {
                    self.next_char();
                    TokenKind::Arrow
                } else {
                    TokenKind::Minus
                }
            }
            '/' => {
                if self.peek_char() == Some('\\') {
                    self.next_char();
                    TokenKind::And
                } else if self.peek_char() == Some('/') {
                    // `//` is the subtype separator `{ x // p }` (one Lean token);
                    // it is never double division. (Lean line comments are `--`.)
                    self.next_char();
                    TokenKind::SlashSlash
                } else {
                    TokenKind::Slash
                }
            }
            '\\' => {
                if self.peek_char() == Some('/') {
                    self.next_char();
                    TokenKind::Or
                } else {
                    // Lean 4 uses raw backslash for set difference: `s \ t`.
                    TokenKind::SDiff
                }
            }
            '<' => {
                match self.peek_char() {
                    Some('=') => {
                        self.next_char();
                        // `<=<` is Bind.kleisliLeft (infixr:55); a bare `<=` is `≤`.
                        if self.peek_char() == Some('<') {
                            self.next_char();
                            TokenKind::KleisliL
                        } else {
                            TokenKind::Le
                        }
                    }
                    Some('*') => {
                        // `<*>` is Seq.seq; `<*` is SeqLeft.seqLeft (both syntax:60).
                        self.next_char();
                        if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::SeqAp // <*>
                        } else {
                            TokenKind::SeqLeft // <*
                        }
                    }
                    Some('&') => {
                        // `<&>` is Functor.mapRev (infixr:100). A bare `<&` is NOT
                        // a Lean token, so only consume the `&` when a `>` follows;
                        // otherwise leave `<` as Lt and let `&` re-lex.
                        let saved_chars = self.chars.clone();
                        let saved_pos = self.pos;
                        self.next_char();
                        if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::MapRev // <&>
                        } else {
                            self.chars = saved_chars;
                            self.pos = saved_pos;
                            TokenKind::Lt
                        }
                    }
                    Some('-') => {
                        self.next_char();
                        TokenKind::LeftArrow // <- (ASCII variant of ←)
                    }
                    Some('$') => {
                        self.next_char();
                        if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::LeftDollarArrow // <$>
                        } else {
                            TokenKind::LeftDollar // <$
                        }
                    }
                    Some('|') => {
                        self.next_char();
                        if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::OrElse // <|>
                        } else {
                            TokenKind::BackwardPipe // <| (backward pipe operator)
                        }
                    }
                    Some(';') => {
                        self.next_char();
                        if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::SeqFocusOp // <;> (tactic sequential focus)
                        } else {
                            // `<;` is not a valid token; backtrack semicolon
                            // and return `<` as Lt, letting the parser handle `;`
                            self.pos -= 1;
                            TokenKind::Lt
                        }
                    }
                    Some(next) if is_angle_operator_char(next) => {
                        // Custom operator composed of angle-like symbols, e.g., <><
                        let mut op = String::from("<");
                        while let Some(c) = self.peek_char() {
                            if is_angle_operator_char(c) {
                                self.next_char();
                                op.push(c);
                            } else {
                                break;
                            }
                        }
                        // `<<<` is the bitwise shift-left operator
                        // (HShiftLeft.hShiftLeft, infixl:75). Every other
                        // angle-symbol cluster stays a custom-notation ident.
                        if op == "<<<" {
                            TokenKind::ShiftL
                        } else {
                            TokenKind::Ident(op)
                        }
                    }
                    _ => TokenKind::Lt,
                }
            }
            '>' => {
                match self.peek_char() {
                    Some('=') => {
                        self.next_char();
                        // `>=>` is Bind.kleisliRight (infixr:55); a bare `>=` is `≥`.
                        if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::KleisliR
                        } else {
                            TokenKind::Ge
                        }
                    }
                    Some('>') => {
                        self.next_char();
                        if self.peek_char() == Some('=') {
                            self.next_char();
                            TokenKind::Bind // >>=
                        } else if self.peek_char() == Some('>') {
                            self.next_char();
                            TokenKind::ShiftR // >>>  (HShiftRight.hShiftRight)
                        } else {
                            TokenKind::Seq // >>
                        }
                    }
                    Some(next) if is_angle_operator_char(next) => {
                        let mut op = String::from(">");
                        while let Some(c) = self.peek_char() {
                            if is_angle_operator_char(c) {
                                self.next_char();
                                op.push(c);
                            } else {
                                break;
                            }
                        }
                        TokenKind::Ident(op)
                    }
                    _ => TokenKind::Gt,
                }
            }
            '!' => {
                if self.peek_char() == Some('=') {
                    self.next_char();
                    // ASCII `!=` is Boolean disequality (`bne`), distinct from
                    // the propositional `≠` (`Ne`) — matching Lean 4.
                    TokenKind::BNe
                } else {
                    TokenKind::Not
                }
            }
            '~' => {
                // Check for ~> (custom arrow operator)
                if self.peek_char() == Some('>') {
                    self.next_char();
                    TokenKind::Ident("~>".to_string())
                } else {
                    TokenKind::Tilde
                }
            }
            '%' => TokenKind::Percent,

            // Unicode
            '→' => {
                // Check for →+* (RingHom)
                if self.peek_char() == Some('+') {
                    let saved_chars = self.chars.clone();
                    let saved_pos = self.pos;
                    self.next_char();
                    if self.peek_char() == Some('*') {
                        self.next_char();
                        TokenKind::Ident("RingHom".to_string())
                    } else {
                        self.chars = saved_chars;
                        self.pos = saved_pos;
                        TokenKind::Arrow
                    }
                } else {
                    TokenKind::Arrow
                }
            }
            'λ' => TokenKind::Lambda,
            '∀' => TokenKind::Forall,
            'Π' => TokenKind::Pi,
            // Temporal-notation glyphs (two-language design §4.2): lex as
            // idents so `prefix:100 "□" => …` custom notation matches by
            // Ident equality — the `~>` precedent — rather than relying on
            // accidental Error-token equality (which worked but made every
            // □/◇ an UnexpectedChar to the rest of the pipeline).
            '□' => TokenKind::Ident("□".to_string()),
            '◇' => TokenKind::Ident("◇".to_string()),
            // U+22A8 ⊨ (TLA-style satisfaction, `M ⊨ φ` — R5 blueprint S4):
            // same ident-lexing treatment as the □/◇ arms so `infix "⊨"`
            // custom notation can match it.
            '⊨' => TokenKind::Ident("⊨".to_string()),
            '∧' => TokenKind::And,
            '∨' => TokenKind::Or,
            '¬' => TokenKind::Not,
            '≤' => TokenKind::Le,
            '≥' => TokenKind::Ge,
            '≠' => TokenKind::Ne,
            '≍' => TokenKind::HEq,      // Heterogeneous equality
            '≈' => TokenKind::Approx,   // HasEquiv.Equiv (setoid/quotient ≈)
            '⊔' => TokenKind::Sup,      // Max.max (lattice join)
            '⊓' => TokenKind::Inf,      // Min.min (lattice meet)
            '⨆' => TokenKind::BigSup,   // iSup (indexed supremum ⨆ i, f i)
            '⨅' => TokenKind::BigInf,   // iInf (indexed infimum ⨅ i, f i)
            '≫' => TokenKind::CatComp,  // CategoryStruct.comp (morphism f ≫ g)
            '⟶' => TokenKind::HomArrow, // Quiver.Hom (morphism type a ⟶ b)
            '⁻' => {
                // `⁻¹` (U+207B SUPERSCRIPT MINUS + U+00B9 SUPERSCRIPT ONE) is the
                // postfix inverse notation `Inv.inv` (Lean `postfix:max "⁻¹"`).
                // The superscript minus only appears as part of this digraph in
                // Lean source; a bare `⁻` is an error.
                if self.peek_char() == Some('¹') {
                    self.next_char(); // consume ¹
                    TokenKind::InvNotation
                } else {
                    TokenKind::Error(LexError::UnexpectedChar('⁻'))
                }
            }
            '≃' => {
                // Check for ≃+* (RingEquiv)
                if self.peek_char() == Some('+') {
                    let saved_chars = self.chars.clone();
                    let saved_pos = self.pos;
                    self.next_char();
                    if self.peek_char() == Some('*') {
                        self.next_char();
                        TokenKind::Ident("RingEquiv".to_string())
                    } else {
                        self.chars = saved_chars;
                        self.pos = saved_pos;
                        TokenKind::Equiv
                    }
                } else if self.peek_char() == Some('*') {
                    // Check for ≃* (MulEquiv)
                    self.next_char();
                    TokenKind::Ident("MulEquiv".to_string())
                } else {
                    TokenKind::Equiv // Plain equivalence/isomorphism
                }
            }
            '⟨' => TokenKind::LAngle,
            '⟩' => TokenKind::RAngle,
            '⟪' => TokenKind::LDAngle,
            '⟫' => TokenKind::RDAngle,
            // ‹ › (U+2039 / U+203A) are the anonymous-hypothesis brackets
            // (`‹P›` desugars to `(show P by assumption)`; Lean `Init/Tactics.lean`).
            '‹' => TokenKind::LFrench,
            '›' => TokenKind::RFrench,
            '↔' => TokenKind::Iff,
            '×' => {
                // `×'` (U+00D7 then ASCII prime) is the anonymous PSigma
                // constructor `(x : T) ×' b`; a bare `×` is Prod / anonymous
                // Sigma. `×ˢ` (SProd) is the Set/Finset product; the `ˢ`
                // (U+02E2 MODIFIER LETTER SMALL S) forms the digraph.
                if self.peek_char() == Some('\'') {
                    self.next_char();
                    TokenKind::TimesPrime
                } else if self.peek_char() == Some('ˢ') {
                    self.next_char();
                    TokenKind::SetProd
                } else {
                    TokenKind::Times
                }
            }
            '⊕' => TokenKind::Oplus,
            // Σ (Greek capital sigma, U+03A3) is reserved notation for the
            // dependent-pair (Sigma) type binder `Σ x : T, body`, never a bare
            // identifier in Lean. `Σ'` is the PSigma binder. Intercept both here
            // before the identifier path.
            'Σ' => {
                if self.peek_char() == Some('\'') {
                    self.next_char();
                    TokenKind::PSigma
                } else {
                    TokenKind::Sigma
                }
            }
            // ∣ (U+2223 DIVIDES) is Dvd.dvd (infix:50) — distinct from the ASCII
            // pattern bar `|` and from `∥`. `▸` (U+25B8) is Term.subst (Eq.rec,
            // trailing:75). `•` (U+2022 BULLET) is HSMul.hSMul (infixr:73) — a
            // different construct from the `·` (U+00B7) section placeholder.
            '∣' => TokenKind::Dvd,
            '▸' => TokenKind::Subst,
            '•' => TokenKind::Smul,
            // ⦃ ⦄ (U+2983 / U+2984) are the strict-implicit binder brackets
            // `fun ⦃x⦄ => …` (BinderInfo.strictImplicit).
            '⦃' => TokenKind::StrictLBrace,
            '⦄' => TokenKind::StrictRBrace,
            '←' => TokenKind::LeftArrow,
            // `↑` (U+2191) is Lean's prefix coercion notation (`↑e` = coerce `e`
            // to the expected type). Lex as an identifier so `↑n` parses as
            // `App(Ident("↑"), [n])`; the elaborator recognizes that head and
            // inserts the coercion. `⇑` (U+21D1, coeFun) is treated the same.
            '↑' => TokenKind::Ident("↑".to_string()),
            '⇑' => TokenKind::Ident("↑".to_string()),
            '∃' => {
                // ∃! (unique existence)
                if self.peek_char() == Some('!') {
                    self.next_char();
                    TokenKind::ExistsUnique
                } else {
                    TokenKind::Exists
                }
            }
            '∈' => TokenKind::Elem,
            '∉' => TokenKind::NotElem,
            '⊆' => TokenKind::Subset,
            '⊂' => TokenKind::ProperSubset,
            '⊢' => TokenKind::Turnstile,
            '∩' => TokenKind::Inter,
            '∪' => TokenKind::Union,
            '∅' => TokenKind::EmptySet,
            '⊤' => TokenKind::Top,
            '⊥' => TokenKind::Bot,
            '↦' => TokenKind::FatArrow, // Unicode mapsto (U+21A6) = fat arrow in lambdas
            '∘' => {
                // Check if followed by prime (') - user-defined operator like ∘'
                if self.peek_char() == Some('\'') {
                    self.next_char();
                    TokenKind::Ident("∘'".to_string())
                } else {
                    TokenKind::Compose
                }
            }
            // `·` (U+00B7 MIDDLE DOT) is the section placeholder (`(· + 1)`).
            // `•` (U+2022 BULLET) is Lean's `HSMul.hSMul` scalar-multiplication
            // operator — a DIFFERENT construct. Conflating them made `a • b`
            // parse as `(a · b)`, a fabricated section (audit P0-4). `•` is not
            // yet implemented, so it falls through to the `UnexpectedChar`
            // catch-all and is rejected loudly in atom position (Brick 1); the
            // real `•` parse lands in Brick 3.
            '·' => TokenKind::Cdot,
            // Blackboard bold letters -> identifiers
            // ℕ+ and ℤ+ are PNat (positive naturals) and PInt notation in Mathlib
            'ℕ' => {
                if self.peek_char() == Some('+') {
                    self.next_char();
                    TokenKind::Ident("PNat".to_string())
                } else {
                    TokenKind::Ident("Nat".to_string())
                }
            }
            'ℤ' => {
                if self.peek_char() == Some('+') {
                    self.next_char();
                    TokenKind::Ident("Int.Positive".to_string())
                } else {
                    TokenKind::Ident("Int".to_string())
                }
            }
            'ℚ' => TokenKind::Ident("Rat".to_string()),
            'ℝ' => TokenKind::Ident("Real".to_string()),
            'ℂ' => TokenKind::Ident("Complex".to_string()),
            // Geometry symbol - angle notation used in MATP/Mathlib
            '∠' => TokenKind::Ident("angle".to_string()),
            // Big operators (Lean 4 / Mathlib notation)
            // ∑' (tsum) and ∑ (Finset.sum) share the same token; the distinction
            // is semantic and handled by the elaborator, not the parser.
            '∑' => {
                // Consume optional trailing prime: ∑' (tsum)
                if self.peek_char() == Some('\'') {
                    self.next_char();
                }
                TokenKind::BigSum
            }
            '∏' => {
                if self.peek_char() == Some('\'') {
                    self.next_char();
                }
                TokenKind::BigProd
            }
            '∫' => {
                if self.peek_char() == Some('\'') {
                    self.next_char();
                }
                TokenKind::Integral
            }
            '⨍' => TokenKind::FintAvg,
            '⋃' => TokenKind::BigUnion,
            '⋂' => TokenKind::BigInter,

            // String literals
            '"' => self.lex_string(start),

            // Character literals: a leading `'` begins a `Char`. Trailing primes
            // in identifiers (e.g. `x'`) are consumed inside `lex_ident`, so a
            // `'` only reaches here at the start of a token.
            '\'' => self.lex_char(),

            // Number literals
            c if c.is_ascii_digit() => self.lex_number(start, c, preceding_char),

            // Raw string literals: `r"..."` and `r#"..."#` / `r##"..."##`.
            // A leading `r` that is immediately followed by `"`, or by one or
            // more `#` then `"`, opens a raw string in which backslashes are
            // literal and embedded quotes are permitted (closed only by `"`
            // followed by the same number of `#`). A bare `r` or any other
            // identifier starting with `r` (e.g. `rabbit`) is NOT a raw string
            // and falls through to `lex_ident` below.
            'r' if self.peek_is_raw_string() => self.lex_raw_string(),

            // Identifiers and keywords
            c if is_ident_start(c) => self.lex_ident(start, c),

            _ => TokenKind::Error(LexError::UnexpectedChar(c)),
        };

        Token::new(
            kind,
            Span::new(start, self.pos),
            preceded_by_newline,
            col,
            line,
        )
    }

    /// Lex a syntax quote starting with a backtick.
    /// Captures either a balanced delimited block or a dotted identifier.
    fn lex_backtick(&mut self, _start: usize) -> TokenKind {
        let mut content = String::new();

        let Some(next) = self.peek_char() else {
            return TokenKind::SyntaxQuote(content);
        };

        if let Some(close) = matching_delim(next) {
            // Quoted block like `(…)`, `[…]`, `{…}`
            self.next_char(); // consume opening delimiter
            content.push(next);
            let mut stack = vec![close];
            while let Some((_, ch)) = self.next_char() {
                content.push(ch);
                if let Some(expected) = stack.last().copied() {
                    if ch == expected {
                        stack.pop();
                        if stack.is_empty() {
                            break;
                        }
                        continue;
                    }
                }
                if let Some(new_close) = matching_delim(ch) {
                    stack.push(new_close);
                }
            }
            if !stack.is_empty() {
                return TokenKind::Error(LexError::UnterminatedSyntaxQuote);
            }
        } else {
            // Quoted identifier or dotted name: `foo, `Foo.bar
            while let Some(c) = self.peek_char() {
                if is_ident_continue(c) || c == '.' {
                    let (_, ch) = self.next_char().expect("peek_char guaranteed a character");
                    content.push(ch);
                    continue;
                }
                if c == '«' {
                    self.next_char();
                    if let Err(err) = self.lex_guillemet_segment(&mut content) {
                        return match err {
                            TokenKind::Error(LexError::UnterminatedQuotedIdent) => {
                                TokenKind::Error(LexError::UnterminatedSyntaxQuote)
                            }
                            _ => err,
                        };
                    }
                    continue;
                }
                break;
            }
        }

        TokenKind::SyntaxQuote(content)
    }

    /// Lex a string literal after the opening `"` has been consumed.
    ///
    /// Reuses the shared escape decoder so string escapes match char-literal
    /// escapes exactly: `\n \t \r \\ \' \" \0`, hex `\xHH`, and unicode
    /// `\u{...}`. The resolved scalar value is pushed into the string buffer.
    /// Malformed escapes surface the same typed `LexError` as char literals,
    /// except that an escape (or the string) truncated by end-of-input reports
    /// `UnterminatedString`.
    fn lex_string(&mut self, _start: usize) -> TokenKind {
        let mut s = String::new();
        loop {
            match self.next_char() {
                Some((_, '"')) => break,
                Some((_, '\\')) => {
                    // Lean 4 string gaps: a backslash immediately followed by
                    // whitespace elides the newline and surrounding whitespace,
                    // letting a string span multiple source lines. The gap must
                    // contain exactly one newline. Anything else is a normal
                    // escape sequence (`\n`, `\t`, `\xHH`, `\u{..}`, ...).
                    if self.peek_char().is_some_and(char::is_whitespace) {
                        if let Some(err) = self.lex_string_gap() {
                            return err;
                        }
                    } else {
                        match self.lex_escape(LexError::UnterminatedString) {
                            Ok(c) => s.push(c),
                            Err(err) => return err,
                        }
                    }
                }
                Some((_, c)) => s.push(c),
                None => return TokenKind::Error(LexError::UnterminatedString),
            }
        }
        TokenKind::StringLit(s)
    }

    /// Consume a Lean 4 string gap after the leading `\` has been consumed and
    /// the next character is known to be whitespace.
    ///
    /// Mirrors upstream `stringGapFn`: whitespace is consumed until the first
    /// non-whitespace character (which is left for the caller to lex), and the
    /// run must contain exactly one newline. The gap contributes no characters
    /// to the string. Returns `Some(error_token)` on a malformed gap (no
    /// newline before non-whitespace, or a second newline) or unterminated
    /// input; `None` on success. Line/column tracking is advanced across the
    /// consumed newline so later diagnostics report accurate positions.
    fn lex_string_gap(&mut self) -> Option<TokenKind> {
        let mut seen_newline = false;
        loop {
            match self.peek_char() {
                Some('\n') => {
                    if seen_newline {
                        return Some(TokenKind::Error(LexError::InvalidStringGap));
                    }
                    seen_newline = true;
                    self.next_char();
                    self.line_start = self.pos;
                    self.line += 1;
                }
                Some(c) if c.is_whitespace() => {
                    self.next_char();
                }
                Some(_) => {
                    if seen_newline {
                        return None;
                    }
                    return Some(TokenKind::Error(LexError::InvalidStringGap));
                }
                None => return Some(TokenKind::Error(LexError::UnterminatedString)),
            }
        }
    }

    /// Lookahead used by the `'r'` dispatch arm: after the leading `r` has been
    /// consumed, does a raw-string opener follow? A raw string opens with `"`
    /// (zero hashes) or with one-or-more `#` immediately followed by `"`. Any
    /// other continuation (including a bare `r`, or `rabbit`-style identifiers)
    /// is not a raw string. Inspects a clone of the cursor and consumes nothing.
    fn peek_is_raw_string(&self) -> bool {
        let mut ahead = self.chars.clone();
        match ahead.next() {
            Some((_, '"')) => true,
            Some((_, '#')) => {
                // One or more `#`, then a `"`, opens the raw string.
                loop {
                    match ahead.next() {
                        Some((_, '#')) => {}
                        Some((_, '"')) => break true,
                        _ => break false,
                    }
                }
            }
            _ => false,
        }
    }

    /// Lex a raw string literal after the leading `r` has been consumed.
    ///
    /// The caller guarantees (via `peek_is_raw_string`) that a valid opener
    /// follows, so the opening hashes and quote are consumed here against the
    /// live cursor. Raw strings perform no escape processing: backslashes are
    /// literal and embedded quotes are permitted. The literal closes at the
    /// first `"` followed by exactly `N` hashes, where `N` is the number of
    /// opening hashes. Reaching end-of-input first yields `UnterminatedString`.
    /// The surface result is the same `StringLit` token as a normal string.
    fn lex_raw_string(&mut self) -> TokenKind {
        // Consume the opening hashes (zero for `r"..."`).
        let mut hashes = 0usize;
        while self.peek_char() == Some('#') {
            self.next_char();
            hashes += 1;
        }
        // Consume the opening quote (guaranteed present by the caller).
        if self.next_char().map(|(_, c)| c) != Some('"') {
            return TokenKind::Error(LexError::UnterminatedString);
        }

        let mut s = String::new();
        loop {
            match self.next_char() {
                Some((_, '"')) => {
                    // A closing quote must be followed by exactly `hashes`
                    // pound signs. If fewer follow (or different content), the
                    // quote and any consumed hashes are part of the contents.
                    let mut closing = 0usize;
                    while closing < hashes && self.peek_char() == Some('#') {
                        self.next_char();
                        closing += 1;
                    }
                    if closing == hashes {
                        break;
                    }
                    // Not a real terminator: keep the quote and the hashes we
                    // consumed as literal content, then continue scanning.
                    s.push('"');
                    for _ in 0..closing {
                        s.push('#');
                    }
                }
                Some((_, c)) => s.push(c),
                None => return TokenKind::Error(LexError::UnterminatedString),
            }
        }
        TokenKind::StringLit(s)
    }

    /// Lex a character literal after the opening `'` has been consumed.
    ///
    /// Accepts a single character or one escape sequence followed by a closing
    /// `'`. Lean 4 char escapes are supported: `\n \t \r \\ \' \" \0`, hex
    /// `\xHH`, and unicode `\u{...}`. Anything that is not exactly one scalar
    /// value, or that lacks a closing quote, is reported as a typed error.
    fn lex_char(&mut self) -> TokenKind {
        // A char literal is single-line: a raw newline before the closing `'`
        // means the literal is unterminated. Stopping at the newline (rather
        // than scanning to the next `'` anywhere in the file) is what prevents a
        // malformed char from swallowing the following declarations — the
        // error-recovery cascade in the gap sweep (literals/p08). Lean's char
        // literals are likewise single-line.
        if self.peek_char() == Some('\n') {
            return TokenKind::Error(LexError::UnterminatedChar);
        }
        let ch = match self.next_char() {
            // Empty literal `''` or a stray `'` at end-of-input.
            Some((_, '\'')) => return TokenKind::Error(LexError::InvalidChar),
            None => return TokenKind::Error(LexError::UnterminatedChar),
            Some((_, '\\')) => match self.lex_char_escape() {
                Ok(c) => c,
                Err(err) => return err,
            },
            Some((_, c)) => c,
        };
        // A newline where the closing `'` should be is an unterminated literal;
        // do NOT consume the newline (that would let the scan below cross into
        // the next line — the swallow this whole guard exists to prevent).
        if self.peek_char() == Some('\n') {
            return TokenKind::Error(LexError::UnterminatedChar);
        }
        match self.next_char() {
            Some((_, '\'')) => TokenKind::CharLit(ch),
            // A second character before the closing quote (`'ab'`). Consume the
            // remaining content up to the closing `'` (or EOF/newline) so the
            // whole malformed literal collapses into one error token rather than
            // leaving a dangling quote that mis-lexes as a fresh char literal —
            // but never cross a newline (see the note above).
            Some(_) => {
                let mut terminated = false;
                while self.peek_char() != Some('\n') {
                    match self.next_char() {
                        Some((_, '\'')) => {
                            terminated = true;
                            break;
                        }
                        Some(_) => {}
                        None => break,
                    }
                }
                if terminated {
                    TokenKind::Error(LexError::InvalidChar)
                } else {
                    TokenKind::Error(LexError::UnterminatedChar)
                }
            }
            None => TokenKind::Error(LexError::UnterminatedChar),
        }
    }

    /// Decode an escape sequence inside a character literal (the leading `\`
    /// has already been consumed). Returns the resolved scalar value.
    fn lex_char_escape(&mut self) -> Result<char, TokenKind> {
        self.lex_escape(LexError::UnterminatedChar)
    }

    /// Decode an escape sequence shared by character and string literals (the
    /// leading `\` has already been consumed). Returns the resolved scalar
    /// value. `eof_err` is the typed error to report when the input ends
    /// mid-escape, so callers can surface `UnterminatedChar` or
    /// `UnterminatedString` as appropriate.
    fn lex_escape(&mut self, eof_err: LexError) -> Result<char, TokenKind> {
        match self.next_char() {
            Some((_, 'n')) => Ok('\n'),
            Some((_, 't')) => Ok('\t'),
            Some((_, 'r')) => Ok('\r'),
            Some((_, '0')) => Ok('\0'),
            Some((_, '\\')) => Ok('\\'),
            Some((_, '\'')) => Ok('\''),
            Some((_, '"')) => Ok('"'),
            Some((_, 'x')) => self.lex_hex_escape(),
            Some((_, 'u')) => self.lex_unicode_escape(eof_err),
            Some((_, c)) => Err(TokenKind::Error(LexError::UnknownEscapeSequence(c))),
            None => Err(TokenKind::Error(eof_err)),
        }
    }

    /// Decode a `\xHH` escape: exactly two hexadecimal digits.
    fn lex_hex_escape(&mut self) -> Result<char, TokenKind> {
        let mut value: u32 = 0;
        for _ in 0..2 {
            match self.peek_char().and_then(|c| c.to_digit(16)) {
                Some(d) => {
                    self.next_char();
                    value = value * 16 + d;
                }
                None => return Err(TokenKind::Error(LexError::InvalidUnicodeEscape)),
            }
        }
        char::from_u32(value).ok_or(TokenKind::Error(LexError::InvalidUnicodeEscape))
    }

    /// Decode a `\u` escape. Two accepted forms, matching Lean's
    /// `quotedCharCoreFn` (`src/Lean/Parser/Basic.lean`):
    /// - `\uXXXX` — exactly four hexadecimal digits, no braces (the Lean-core
    ///   form: `"A"` is `A`, `'α'` is `α`);
    /// - `\u{...}` — one or more hex digits inside braces (retained superset).
    /// `eof_err` is the typed error to report when the input ends mid-escape
    /// (`UnterminatedChar` vs `UnterminatedString`).
    fn lex_unicode_escape(&mut self, eof_err: LexError) -> Result<char, TokenKind> {
        // Braceless `\uXXXX`: exactly four hex digits.
        if self.peek_char() != Some('{') {
            let mut value: u32 = 0;
            for _ in 0..4 {
                match self.peek_char() {
                    Some(c) => match c.to_digit(16) {
                        Some(d) => {
                            self.next_char();
                            value = value * 16 + d;
                        }
                        None => return Err(TokenKind::Error(LexError::InvalidUnicodeEscape)),
                    },
                    None => return Err(TokenKind::Error(eof_err)),
                }
            }
            return char::from_u32(value).ok_or(TokenKind::Error(LexError::InvalidUnicodeEscape));
        }
        // Braced `\u{...}`.
        if self.next_char().map(|(_, c)| c) != Some('{') {
            return Err(TokenKind::Error(LexError::InvalidUnicodeEscape));
        }
        let mut value: u32 = 0;
        let mut saw_digit = false;
        loop {
            match self.peek_char() {
                Some('}') => {
                    self.next_char();
                    break;
                }
                Some(c) => match c.to_digit(16) {
                    Some(d) => {
                        self.next_char();
                        saw_digit = true;
                        value = match value.checked_mul(16).and_then(|v| v.checked_add(d)) {
                            Some(v) => v,
                            None => return Err(TokenKind::Error(LexError::InvalidUnicodeEscape)),
                        };
                    }
                    None => return Err(TokenKind::Error(LexError::InvalidUnicodeEscape)),
                },
                None => return Err(TokenKind::Error(eof_err)),
            }
        }
        if !saw_digit {
            return Err(TokenKind::Error(LexError::InvalidUnicodeEscape));
        }
        char::from_u32(value).ok_or(TokenKind::Error(LexError::InvalidUnicodeEscape))
    }

    /// Lex the body of an interpolated string (after consuming the opening `"`).
    ///
    /// Preserves the raw content between quotes so that `parse_interpolation` can
    /// process `{expr}` segments and escape sequences. Tracks brace depth so that
    /// nested `{...}` inside interpolation expressions don't prematurely terminate
    /// the string.
    fn lex_interpolated_string(&mut self, kind: InterpolatedStringKind) -> TokenKind {
        let mut s = String::new();
        let mut brace_depth: u32 = 0;
        loop {
            match self.next_char() {
                Some((_, '"')) if brace_depth == 0 => break,
                Some((_, '\\')) => {
                    // Preserve escape sequences verbatim for parse_interpolation
                    s.push('\\');
                    match self.next_char() {
                        Some((_, c)) => s.push(c),
                        None => return TokenKind::Error(LexError::UnterminatedString),
                    }
                }
                Some((_, '{')) => {
                    brace_depth += 1;
                    s.push('{');
                }
                Some((_, '}')) => {
                    brace_depth = brace_depth.saturating_sub(1);
                    s.push('}');
                }
                Some((_, c)) => s.push(c),
                None => return TokenKind::Error(LexError::UnterminatedString),
            }
        }
        TokenKind::InterpolatedString(kind, s)
    }

    fn lex_guillemet_ident(&mut self) -> TokenKind {
        let mut s = String::new();
        let mut escaped = true;
        if let Err(err) = self.lex_guillemet_segment(&mut s) {
            return err;
        }
        if let Err(err) = self.lex_ident_tail(&mut s, &mut escaped) {
            return err;
        }
        TokenKind::Ident(s)
    }

    fn lex_number(
        &mut self,
        _start: usize,
        first: char,
        preceding_char: Option<char>,
    ) -> TokenKind {
        // Detect Lean 4 radix prefixes: a leading `0` followed by a base marker
        // selects hex (`0x`/`0X`), binary (`0b`/`0B`), or octal (`0o`/`0O`).
        // Anything else (including a bare `0`) is decimal. Underscores are
        // permitted as digit-group separators in every base (e.g. `0xFF_FF`).
        if first == '0' {
            if let Some(radix) = self.peek_char().and_then(radix_for_marker) {
                self.next_char(); // consume the base marker (x/X, b/B, o/O)
                return self.lex_radix_digits(radix);
            }
        }
        // Decimal path: `first` is guaranteed by the caller to be an ASCII digit.
        let mut n: u64 = match first.to_digit(10) {
            Some(d) => u64::from(d),
            None => return TokenKind::Error(LexError::NumericOverflow),
        };
        // Accumulate the textual form (underscores stripped) so a float can be
        // reparsed via `f64::from_str` while integers keep their exact `u64`.
        let mut text = String::new();
        text.push(first);
        let mut overflowed = false;
        while let Some(c) = self.peek_char() {
            if let Some(d) = c.to_digit(10) {
                self.next_char();
                text.push(c);
                if !overflowed {
                    match n
                        .checked_mul(10)
                        .and_then(|value| value.checked_add(u64::from(d)))
                    {
                        Some(value) => n = value,
                        None => overflowed = true,
                    }
                }
            } else if c == '_' {
                // Allow underscores in numbers: 1_000_000
                self.next_char();
            } else {
                break;
            }
        }

        // Float detection. A decimal point is part of a float ONLY when it is
        // immediately followed by an ASCII digit (`3.14`). A `.` followed by an
        // identifier is field projection (`x.foo`), and `..` is the range
        // operator (`1..2`); both must leave the integer intact. An exponent
        // marker (`e`/`E`) — optionally signed — also yields a float (`1e-5`).
        // A digit that is itself a PROJECTION INDEX (immediately after a `.`)
        // must not absorb a following `.<digit>` as a fractional part: `s.2.1` is
        // `(s.2).1`, not `s . 2.1`. Suppress float detection in that case.
        let in_projection = preceding_char == Some('.');
        let mut is_float = false;
        if !in_projection && self.peek_char() == Some('.') && self.peek_char_after_dot_is_digit() {
            is_float = true;
            self.next_char(); // consume '.'
            text.push('.');
            self.consume_fraction_digits(&mut text);
        }
        if self.peek_exponent_follows() {
            is_float = true;
            self.consume_exponent(&mut text);
        }

        if is_float {
            // The accumulated `text` is well-formed by construction (digits,
            // a single `.`, and an optional validated exponent), so it is kept
            // verbatim rather than rounded through an `f64`.
            return TokenKind::FloatLit(text);
        }

        if overflowed {
            // The `u64` accumulator wrapped (value >= 2^64). Lean `Nat` literals
            // are unbounded, so re-fold the exact integer digits into an
            // arbitrary-precision `BigNat`. `text` holds only the integer digits
            // here (float handling returned above; underscores were never
            // pushed), so a base-10 fold reproduces the exact value.
            match BigNat::from_radix_str(&text, 10) {
                Some(big) => TokenKind::NatLit(big),
                // Only a pathological literal beyond the multi-limb cap declines.
                None => TokenKind::Error(LexError::NumericOverflow),
            }
        } else {
            TokenKind::NatLit(BigNat::Small(n))
        }
    }

    /// Lex a leading-dot float (`.5` => `0.5`) after the opening `.` has been
    /// consumed. The caller has already confirmed the next character is an
    /// ASCII digit and that the `.` sits at a token boundary. The normalized
    /// text is prefixed with `0` so it parses as a standard float, and the
    /// fractional digits and an optional exponent reuse the shared number
    /// helpers (`1e-5`-style exponents are supported, e.g. `.25e3`).
    fn lex_leading_dot_float(&mut self) -> TokenKind {
        // Normalize `.5` to `0.5`: prefix the implicit integer part.
        let mut text = String::from("0.");
        self.consume_fraction_digits(&mut text);
        if self.peek_exponent_follows() {
            self.consume_exponent(&mut text);
        }
        TokenKind::FloatLit(text)
    }

    /// Lookahead: is the character *after* the upcoming `.` an ASCII digit?
    /// Clones the iterator so the lexer position is untouched. Used to keep
    /// `1.foo` (projection) and `1..2` (range) from being read as floats.
    fn peek_char_after_dot_is_digit(&self) -> bool {
        let mut ahead = self.chars.clone();
        // First element is the '.' itself (already confirmed by the caller).
        ahead.next();
        matches!(ahead.next(), Some((_, c)) if c.is_ascii_digit())
    }

    /// Consume the fractional digits after a decimal point, appending them to
    /// `text` (underscores stripped as elsewhere).
    fn consume_fraction_digits(&mut self, text: &mut String) {
        while let Some(c) = self.peek_char() {
            if c.is_ascii_digit() {
                self.next_char();
                text.push(c);
            } else if c == '_' {
                self.next_char();
            } else {
                break;
            }
        }
    }

    /// Lookahead: does a well-formed exponent (`e`/`E`, optional sign, then at
    /// least one digit) begin at the current position? A bare `e` with no
    /// following digit is an identifier, not an exponent (`1e` => `1` then `e`).
    fn peek_exponent_follows(&self) -> bool {
        let mut ahead = self.chars.clone();
        match ahead.next() {
            Some((_, 'e' | 'E')) => {}
            _ => return false,
        }
        let mut next = ahead.next().map(|(_, c)| c);
        if matches!(next, Some('+' | '-')) {
            next = ahead.next().map(|(_, c)| c);
        }
        matches!(next, Some(c) if c.is_ascii_digit())
    }

    /// Consume a validated exponent (caller checked via `peek_exponent_follows`).
    fn consume_exponent(&mut self, text: &mut String) {
        if let Some((_, e)) = self.next_char() {
            text.push(e); // 'e' or 'E'
        }
        if matches!(self.peek_char(), Some('+' | '-')) {
            if let Some((_, sign)) = self.next_char() {
                text.push(sign);
            }
        }
        self.consume_fraction_digits(text);
    }

    /// Accumulate the digits of a non-decimal literal after its base marker
    /// (`0x`/`0b`/`0o`) has been consumed. `radix` is one of 16/2/8. At least
    /// one valid digit must follow the marker; otherwise the literal is
    /// rejected as a numeric error rather than silently mis-lexing.
    fn lex_radix_digits(&mut self, radix: u32) -> TokenKind {
        let mut n: u64 = 0;
        let mut saw_digit = false;
        let mut overflowed = false;
        // Retain the exact digit chars so an overflowing (>= 2^64) literal can be
        // re-folded into an arbitrary-precision `BigNat`. Only populated once the
        // `u64` fast path wraps, so small literals allocate nothing here.
        let mut digits = String::new();
        while let Some(c) = self.peek_char() {
            if let Some(d) = c.to_digit(radix) {
                self.next_char();
                saw_digit = true;
                if overflowed {
                    digits.push(c);
                } else {
                    match n
                        .checked_mul(u64::from(radix))
                        .and_then(|value| value.checked_add(u64::from(d)))
                    {
                        Some(value) => n = value,
                        None => {
                            // Reconstruct the digits seen so far (the u64 value
                            // `n`, printed in this radix) and continue collecting
                            // in arbitrary precision from this point on.
                            overflowed = true;
                            digits = to_radix_digits(n, radix);
                            digits.push(c);
                        }
                    }
                }
            } else if c == '_' {
                // Allow digit-group separators: 0xFF_FF, 0b1010_1010
                self.next_char();
            } else {
                break;
            }
        }
        if !saw_digit {
            return TokenKind::Error(LexError::NumericOverflow);
        }
        if overflowed {
            // Lean `Nat` literals are unbounded: re-fold the exact digits in the
            // literal's own base rather than rejecting the >= 2^64 value.
            match BigNat::from_radix_str(&digits, radix) {
                Some(big) => TokenKind::NatLit(big),
                None => TokenKind::Error(LexError::NumericOverflow),
            }
        } else {
            TokenKind::NatLit(BigNat::Small(n))
        }
    }

    fn lex_ident(&mut self, _start: usize, first: char) -> TokenKind {
        let mut s = String::new();
        let mut escaped = false;
        s.push(first);
        if let Err(err) = self.lex_ident_tail(&mut s, &mut escaped) {
            return err;
        }

        if escaped {
            return TokenKind::Ident(s);
        }

        // Check for interpolated string prefixes: s!", m!", f!"
        if self.peek_char() == Some('"') {
            let kind = match s.as_str() {
                "s!" => Some(InterpolatedStringKind::String),
                "m!" => Some(InterpolatedStringKind::MessageData),
                "f!" => Some(InterpolatedStringKind::Format),
                _ => None,
            };
            if let Some(kind) = kind {
                self.next_char(); // consume opening '"'
                return self.lex_interpolated_string(kind);
            }
        }

        // Check for keywords
        match s.as_str() {
            "def" => TokenKind::Def,
            "theorem" => TokenKind::Theorem,
            "lemma" => TokenKind::Lemma,
            "axiom" => TokenKind::Axiom,
            "opaque" => TokenKind::Opaque,
            "example" => TokenKind::Example,
            "let" => TokenKind::Let,
            "in" => TokenKind::In,
            "fun" => TokenKind::Fun,
            "forall" => TokenKind::Forall,
            "if" => TokenKind::If,
            "then" => TokenKind::Then,
            "else" => TokenKind::Else,
            "match" => TokenKind::Match,
            "with" => TokenKind::With,
            "where" => TokenKind::Where,
            "do" => TokenKind::Do,
            "return" => TokenKind::Return,
            "structure" => TokenKind::Structure,
            "class" => TokenKind::Class,
            "instance" => TokenKind::Instance,
            "inductive" => TokenKind::Inductive,
            "coinductive" => TokenKind::Coinductive,
            "deriving" => TokenKind::Deriving,
            "namespace" => TokenKind::Namespace,
            "section" => TokenKind::Section,
            "end" => TokenKind::End,
            "open" => TokenKind::Open,
            "export" => TokenKind::Export,
            "variable" => TokenKind::Variable,
            "universe" => TokenKind::Universe,
            "import" => TokenKind::Import,
            "mutual" => TokenKind::Mutual,
            "set_option" => TokenKind::SetOption,
            "by" => TokenKind::By,
            "have" => TokenKind::Have,
            "show" => TokenKind::Show,
            "suffices" => TokenKind::Suffices,
            "from" => TokenKind::From,
            "rfl" => TokenKind::Rfl,
            "sorry" => TokenKind::Sorry,
            "extends" => TokenKind::Extends,
            "private" => TokenKind::Private,
            "protected" => TokenKind::Protected,
            "public" => TokenKind::Public,
            "module" => TokenKind::Module,
            "partial" => TokenKind::Partial,
            "unsafe" => TokenKind::Unsafe,
            "noncomputable" => TokenKind::Noncomputable,
            "abbrev" => TokenKind::Abbrev,
            "attribute" => TokenKind::Attribute,
            "syntax" => TokenKind::Syntax,
            "macro" => TokenKind::Macro,
            "macro_rules" => TokenKind::MacroRules,
            "elab" => TokenKind::Elab,
            "infixl" => TokenKind::Infixl,
            "infixr" => TokenKind::Infixr,
            "infix" => TokenKind::Infix,
            "prefix" => TokenKind::Prefix,
            "postfix" => TokenKind::Postfix,
            "notation" => TokenKind::Notation,
            "scoped" => TokenKind::Scoped,
            "hiding" => TokenKind::Hiding,
            "renaming" => TokenKind::Renaming,
            "rec" => TokenKind::Rec,
            "Type" => TokenKind::Type,
            "Prop" => TokenKind::Prop,
            "Sort" => TokenKind::Sort,
            _ => TokenKind::Ident(s),
        }
    }

    fn lex_ident_tail(&mut self, s: &mut String, escaped: &mut bool) -> Result<(), TokenKind> {
        loop {
            match self.peek_char() {
                Some(c) if is_ident_continue(c) => {
                    s.push(c);
                    self.next_char();
                }
                Some('«') => {
                    *escaped = true;
                    self.next_char();
                    self.lex_guillemet_segment(s)?;
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn lex_guillemet_segment(&mut self, s: &mut String) -> Result<(), TokenKind> {
        let mut saw_char = false;
        loop {
            match self.next_char() {
                Some((_, '»')) => {
                    if !saw_char {
                        return Err(TokenKind::Error(LexError::EmptyQuotedIdent));
                    }
                    return Ok(());
                }
                Some((_, c)) => {
                    saw_char = true;
                    s.push(c);
                }
                None => {
                    return Err(TokenKind::Error(LexError::UnterminatedQuotedIdent));
                }
            }
        }
    }
}

/// The Unicode "Spacing Modifier Letters" block (U+02B0..=U+02FF, includes `ˢ`,
/// `ˡ`, `ʰ`, …). Rust's `char::is_alphabetic`/`is_alphanumeric` return `true`
/// for these (general category `Lm`), but Lean's `isIdFirst`/`isIdRest` use a
/// closed whitelist that EXCLUDES them (`Init/Meta/Defs.lean`). Treating them as
/// identifier characters mis-lexes `×ˢ` (Mathlib `SProd.sprod`) into
/// `Prod a (ˢ b)` instead of erroring, and swallows a stray `ˢ` into a preceding
/// name. Excluding them makes clean reject them loudly, matching Lean's
/// "expected token".
fn is_modifier_letter(c: char) -> bool {
    ('\u{02B0}'..='\u{02FF}').contains(&c)
}

fn is_ident_start(c: char) -> bool {
    !is_modifier_letter(c)
        && (c.is_alphabetic() || c == '_' || (c.is_numeric() && !c.is_ascii_digit()))
}

/// Map a Lean 4 numeric base marker (the character following a leading `0`)
/// to its radix: `x`/`X` -> 16, `b`/`B` -> 2, `o`/`O` -> 8.
fn radix_for_marker(c: char) -> Option<u32> {
    match c {
        'x' | 'X' => Some(16),
        'b' | 'B' => Some(2),
        'o' | 'O' => Some(8),
        _ => None,
    }
}

/// Render a `u64` as its digit string in `radix` (2..=16). Used to reconstruct
/// the digits already consumed on the `u64` fast path at the exact moment it
/// overflows, so the arbitrary-precision fold can resume from an equal value.
fn to_radix_digits(mut n: u64, radix: u32) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let base = u64::from(radix);
    let mut buf = Vec::new();
    while n > 0 {
        let digit = u32::try_from(n % base).unwrap_or(0);
        buf.push(std::char::from_digit(digit, radix).unwrap_or('0'));
        n /= base;
    }
    buf.iter().rev().collect()
}

fn is_ident_continue(c: char) -> bool {
    !is_modifier_letter(c) && (c.is_alphanumeric() || c == '_' || c == '\'' || c == '?' || c == '!')
}

/// Whether a `.` *immediately preceded* by `prev` may begin a leading-dot
/// float (`.5` => `0.5`). It may only do so when the `.` is not glued to a
/// preceding expression: not directly after an identifier/number continuation
/// character (`x.5`, `1.5` — though the latter is handled in `lex_number`) and
/// not after a closing delimiter (`(x).5`, `xs[0].5`). In those cases the `.`
/// is a projection dot and is left untouched. Whitespace, opening delimiters,
/// operators, commas, etc. all permit the leading-dot float.
fn starts_leading_dot_float(prev: char) -> bool {
    // `·` is a section placeholder that stands for an expression, so a following
    // `.<digit>` is a PROJECTION on it (`(·.1)` = `fun x => x.1`), never the
    // placeholder applied to a leading-dot float — treat `·` like a closing
    // delimiter here. Without this, `·.1` lexed `.1` as the float `0.1`, so
    // `(·.1)` desugared to `fun x => x 0.1` (an application) and failed to
    // elaborate, while `(·.snd)` (a named projection) worked.
    !is_ident_continue(prev) && !matches!(prev, ')' | ']' | '}' | '⟩' | '·')
}

fn matching_delim(c: char) -> Option<char> {
    match c {
        '(' => Some(')'),
        '[' => Some(']'),
        '{' => Some('}'),
        '⟨' => Some('⟩'),
        _ => None,
    }
}

fn is_angle_operator_char(c: char) -> bool {
    c == '<' || c == '>'
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(input: &str) -> Vec<TokenKind> {
        Lexer::tokenize(input)
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| *k != TokenKind::Eof)
            .collect()
    }

    #[test]
    fn test_keywords() {
        assert_eq!(lex("def"), vec![TokenKind::Def]);
        assert_eq!(lex("theorem"), vec![TokenKind::Theorem]);
        assert_eq!(lex("let"), vec![TokenKind::Let]);
        assert_eq!(lex("fun"), vec![TokenKind::Fun]);
        assert_eq!(lex("forall"), vec![TokenKind::Forall]);
        assert_eq!(lex("Type"), vec![TokenKind::Type]);
        assert_eq!(lex("Prop"), vec![TokenKind::Prop]);
    }

    #[test]
    fn test_bitwise_and_boolean_operators() {
        // Multi-char bitwise / boolean operators lex to dedicated tokens.
        assert_eq!(lex("&&&"), vec![TokenKind::BitAnd]);
        assert_eq!(lex("|||"), vec![TokenKind::BitOr]);
        assert_eq!(lex("^^^"), vec![TokenKind::BitXor]);
        assert_eq!(lex("<<<"), vec![TokenKind::ShiftL]);
        assert_eq!(lex(">>>"), vec![TokenKind::ShiftR]);
        assert_eq!(lex("&&"), vec![TokenKind::AmpAmp]);
        assert_eq!(lex("||"), vec![TokenKind::PipePipe]);
    }

    #[test]
    fn test_bitwise_operators_do_not_clobber_shorter_tokens() {
        // A bare `&`/`|`/`^` stays its original single token.
        assert_eq!(lex("&"), vec![TokenKind::Amp]);
        assert_eq!(lex("|"), vec![TokenKind::Pipe]);
        assert_eq!(lex("^"), vec![TokenKind::Caret]);
        // `^^` is NOT a Lean operator: only the full `^^^` collapses, so a stray
        // double caret backtracks to two single `^` tokens (HPow chain).
        assert_eq!(lex("^^"), vec![TokenKind::Caret, TokenKind::Caret]);
        // `>>` and `>>=` are unaffected by the `>>>` addition.
        assert_eq!(lex(">>"), vec![TokenKind::Seq]);
        assert_eq!(lex(">>="), vec![TokenKind::Bind]);
        // `|>` / `|-` still take priority over `||`.
        // `|>` is the forward pipe operator (its own token, not `RAngle`).
        assert_eq!(lex("|>"), vec![TokenKind::ForwardPipe]);
        assert_eq!(lex("|-"), vec![TokenKind::Turnstile]);
        // `m &&& n` lexes as a single operator flanked by identifiers.
        assert_eq!(
            lex("m &&& n"),
            vec![
                TokenKind::Ident("m".to_string()),
                TokenKind::BitAnd,
                TokenKind::Ident("n".to_string()),
            ]
        );
    }

    #[test]
    fn test_temporal_glyphs_lex_as_idents() {
        // □/◇ (landed) and U+22A8 ⊨ (R5 blueprint S4) lex as Ident tokens so
        // custom notation (`prefix "□"`, `infix "⊨"`) matches by Ident
        // equality; ⊨ round-trips through the lexer instead of erroring.
        assert_eq!(lex("□"), vec![TokenKind::Ident("□".to_string())]);
        assert_eq!(lex("◇"), vec![TokenKind::Ident("◇".to_string())]);
        assert_eq!(lex("⊨"), vec![TokenKind::Ident("⊨".to_string())]);
        assert_eq!(
            lex("M ⊨ φ"),
            vec![
                TokenKind::Ident("M".to_string()),
                TokenKind::Ident("⊨".to_string()),
                TokenKind::Ident("φ".to_string()),
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(lex("foo"), vec![TokenKind::Ident("foo".to_string())]);
        assert_eq!(lex("Nat"), vec![TokenKind::Ident("Nat".to_string())]);
        assert_eq!(lex("x'"), vec![TokenKind::Ident("x'".to_string())]);
        // Test that keyword followed by underscore is an identifier, not keyword + underscore
        assert_eq!(
            lex("opaque_"),
            vec![TokenKind::Ident("opaque_".to_string())]
        );
        assert_eq!(lex("let_"), vec![TokenKind::Ident("let_".to_string())]);
        assert_eq!(
            lex("is_valid?"),
            vec![TokenKind::Ident("is_valid?".to_string())]
        );
        assert_eq!(
            lex("«»"),
            vec![TokenKind::Error(LexError::EmptyQuotedIdent)]
        );
        assert_eq!(lex("«if»"), vec![TokenKind::Ident("if".to_string())]);
        assert_eq!(
            lex("«foo.bar»"),
            vec![TokenKind::Ident("foo.bar".to_string())]
        );
        assert_eq!(lex("«if»foo"), vec![TokenKind::Ident("iffoo".to_string())]);
        assert_eq!(
            lex("«foo bar»"),
            vec![TokenKind::Ident("foo bar".to_string())]
        );
        assert_eq!(
            lex("prefix«test»foo"),
            vec![TokenKind::Ident("prefixtestfoo".to_string())]
        );
        assert_eq!(
            lex("«test»foo"),
            vec![TokenKind::Ident("testfoo".to_string())]
        );
        // Guillemet error cases
        assert_eq!(
            lex("«foo"),
            vec![TokenKind::Error(LexError::UnterminatedQuotedIdent)]
        );
        assert_eq!(
            lex("foo«bar"),
            vec![TokenKind::Error(LexError::UnterminatedQuotedIdent)]
        );
        // Newlines in guillemet identifiers are allowed (Lean 4 permits this)
        assert_eq!(
            lex("«foo\nbar»"),
            vec![TokenKind::Ident("foo\nbar".to_string())]
        );
        // Regression test for #239: underscore followed by prime/question/bang
        assert_eq!(lex("_'"), vec![TokenKind::Ident("_'".to_string())]);
        assert_eq!(lex("_?"), vec![TokenKind::Ident("_?".to_string())]);
        assert_eq!(lex("_!"), vec![TokenKind::Ident("_!".to_string())]);
    }

    #[test]
    fn test_syntax_quote_identifiers() {
        assert_eq!(lex("`foo"), vec![TokenKind::SyntaxQuote("foo".to_string())]);
        assert_eq!(
            lex("`Foo.bar"),
            vec![TokenKind::SyntaxQuote("Foo.bar".to_string())]
        );
        assert_eq!(
            lex("`«foo bar»"),
            vec![TokenKind::SyntaxQuote("foo bar".to_string())]
        );
        assert_eq!(
            lex("`Foo.«bar baz»"),
            vec![TokenKind::SyntaxQuote("Foo.bar baz".to_string())]
        );
        assert_eq!(
            lex("`«»"),
            vec![TokenKind::Error(LexError::EmptyQuotedIdent)]
        );
    }

    #[test]
    fn test_syntax_quote_unterminated() {
        assert_eq!(
            lex("`(foo"),
            vec![TokenKind::Error(LexError::UnterminatedSyntaxQuote)]
        );
        assert_eq!(
            lex("`Foo.«bar"),
            vec![TokenKind::Error(LexError::UnterminatedSyntaxQuote)]
        );
    }

    #[test]
    fn test_syntax_quote_angle_delim() {
        assert_eq!(
            lex("`⟨foo⟩"),
            vec![TokenKind::SyntaxQuote("⟨foo⟩".to_string())]
        );
    }

    #[test]
    fn test_numbers() {
        assert_eq!(lex("0"), vec![TokenKind::nat_lit(0)]);
        assert_eq!(lex("42"), vec![TokenKind::nat_lit(42)]);
        assert_eq!(lex("1_000_000"), vec![TokenKind::nat_lit(1_000_000)]);
    }

    #[test]
    fn test_decimal_value_pinning() {
        // Regression: plain decimal literals keep their exact value.
        assert_eq!(lex("42"), vec![TokenKind::nat_lit(42)]);
        assert_eq!(lex("0"), vec![TokenKind::nat_lit(0)]);
        assert_eq!(lex("1_000"), vec![TokenKind::nat_lit(1000)]);
    }

    #[test]
    fn test_hex_literal_values() {
        // Lean 4: 0xFF == 255, hex is case-insensitive for both marker and digits.
        assert_eq!(lex("0xFF"), vec![TokenKind::nat_lit(255)]);
        assert_eq!(lex("0xff"), vec![TokenKind::nat_lit(255)]);
        assert_eq!(lex("0XfF"), vec![TokenKind::nat_lit(255)]);
        assert_eq!(lex("0x1A2B"), vec![TokenKind::nat_lit(0x1A2B)]);
        // Underscore digit separators are allowed within any base: 0xFF_FF == 65535.
        assert_eq!(lex("0xFF_FF"), vec![TokenKind::nat_lit(65_535)]);
    }

    #[test]
    fn test_binary_literal_values() {
        // Lean 4: 0b1010 == 10.
        assert_eq!(lex("0b1010"), vec![TokenKind::nat_lit(10)]);
        assert_eq!(lex("0B1111"), vec![TokenKind::nat_lit(15)]);
        assert_eq!(lex("0b1010_1010"), vec![TokenKind::nat_lit(0b1010_1010)]);
    }

    #[test]
    fn test_octal_literal_values() {
        // Lean 4: 0o777 == 511.
        assert_eq!(lex("0o777"), vec![TokenKind::nat_lit(511)]);
        assert_eq!(lex("0O10"), vec![TokenKind::nat_lit(8)]);
    }

    #[test]
    fn test_radix_zero_values() {
        // A leading zero with a base marker and a zero digit is still zero.
        assert_eq!(lex("0x0"), vec![TokenKind::nat_lit(0)]);
        assert_eq!(lex("0b0"), vec![TokenKind::nat_lit(0)]);
        assert_eq!(lex("0o0"), vec![TokenKind::nat_lit(0)]);
    }

    #[test]
    fn test_radix_at_or_above_u64_boundary_is_arbitrary_precision() {
        // B27: literals >= 2^64 are NOT overflow errors — Lean `Nat` is
        // unbounded, so they lex to an exact multi-limb `BigNat`.
        // 0x1_0000_0000_0000_0000 == 2^64 == [0, 1] little-endian.
        assert_eq!(
            lex("0x10000000000000000"),
            vec![TokenKind::NatLit(BigNat::from_limbs(vec![0, 1]))]
        );
        // 0xFFFF_FFFF_FFFF_FFFF == u64::MAX stays on the small fast path.
        assert_eq!(
            lex("0xFFFFFFFFFFFFFFFF"),
            vec![TokenKind::nat_lit(u64::MAX)]
        );
        // u64::MAX + 1 == 2^64 via decimal, hex, binary, and octal all agree.
        let two_pow_64 = BigNat::from_limbs(vec![0, 1]);
        assert_eq!(
            lex("18446744073709551616"),
            vec![TokenKind::NatLit(two_pow_64.clone())]
        );
        // octal: 2·8^21 = 2·2^63 = 2^64.
        assert_eq!(
            lex("0o2000000000000000000000"),
            vec![TokenKind::NatLit(two_pow_64.clone())]
        );
        assert_eq!(
            lex("0b10000000000000000000000000000000000000000000000000000000000000000"),
            vec![TokenKind::NatLit(two_pow_64)]
        );
    }

    #[test]
    fn test_radix_marker_without_digits_is_error() {
        // A base marker with no following digit is malformed, not a silent split.
        assert_eq!(lex("0x"), vec![TokenKind::Error(LexError::NumericOverflow)]);
        assert_eq!(lex("0b"), vec![TokenKind::Error(LexError::NumericOverflow)]);
    }

    #[test]
    fn test_radix_stops_at_out_of_range_digit() {
        // `0b102` -> binary `10` (==2) then decimal `2` as a separate literal,
        // because `2` is not a valid binary digit.
        assert_eq!(
            lex("0b102"),
            vec![TokenKind::nat_lit(2), TokenKind::nat_lit(2)]
        );
        // `0o18` -> octal `1` then decimal `8`.
        assert_eq!(
            lex("0o18"),
            vec![TokenKind::nat_lit(1), TokenKind::nat_lit(8)]
        );
    }

    #[test]
    fn test_decimal_at_or_above_u64_boundary_is_arbitrary_precision() {
        // B27: `2^64` decimal used to be rejected as a u64 overflow; it now
        // lexes to the exact multi-limb `BigNat` value `[0, 1]` (little-endian).
        assert_eq!(
            lex("18446744073709551616"),
            vec![TokenKind::NatLit(BigNat::from_limbs(vec![0, 1]))]
        );
        // u64::MAX stays on the compact small fast path.
        assert_eq!(
            lex("18446744073709551615"),
            vec![TokenKind::nat_lit(u64::MAX)]
        );
        // A 100-digit decimal round-trips exactly (folded, not truncated).
        let hundred = "1".to_string() + &"0".repeat(99);
        let expected = BigNat::from_radix_str(&hundred, 10).expect("100-digit decimal folds");
        assert_eq!(lex(&hundred), vec![TokenKind::NatLit(expected)]);
    }

    /// Helper: the single `FloatLit` token expected for a well-formed float.
    fn float_tok(text: &str) -> Vec<TokenKind> {
        vec![TokenKind::FloatLit(text.to_string())]
    }

    #[test]
    fn test_float_simple_decimal_point() {
        // `3.5` is a single float token, not `3` `.` `5`.
        assert_eq!(lex("3.5"), float_tok("3.5"));
        assert_eq!(lex("0.0"), float_tok("0.0"));
        // Underscores remain legal digit-group separators in floats and are
        // stripped from the normalized text.
        assert_eq!(lex("1_000.5"), float_tok("1000.5"));
    }

    #[test]
    fn test_float_with_exponent() {
        // The exponent marker's case is preserved verbatim in the source text.
        assert_eq!(lex("2.5E10"), float_tok("2.5E10"));
        assert_eq!(lex("1.0e3"), float_tok("1.0e3"));
        // Exponent with no fractional part is still a float (`1e10`).
        assert_eq!(lex("1e10"), float_tok("1e10"));
    }

    #[test]
    fn test_float_negative_exponent() {
        assert_eq!(lex("1e-5"), float_tok("1e-5"));
        assert_eq!(lex("2.5e+3"), float_tok("2.5e+3"));
        assert_eq!(lex("6.022E-23"), float_tok("6.022E-23"));
    }

    #[test]
    fn test_range_operator_stays_two_nats() {
        // `1..2` must lex as NatLit(1), DotDot, NatLit(2) — never a float.
        assert_eq!(
            lex("1..2"),
            vec![
                TokenKind::nat_lit(1),
                TokenKind::DotDot,
                TokenKind::nat_lit(2)
            ]
        );
    }

    #[test]
    fn test_digit_dot_ident_stays_projection() {
        // `1.foo` is integer projection, not a float: NatLit(1), Dot, Ident(foo).
        assert_eq!(
            lex("1.foo"),
            vec![
                TokenKind::nat_lit(1),
                TokenKind::Dot,
                TokenKind::Ident("foo".to_string())
            ]
        );
    }

    #[test]
    fn test_leading_dot_float_normalizes_with_zero_prefix() {
        // `.5` is the float `0.5`; the implicit integer part is prefixed.
        assert_eq!(lex(".5"), float_tok("0.5"));
        assert_eq!(lex(".0"), float_tok("0.0"));
        // Underscores remain legal digit-group separators and are stripped.
        assert_eq!(lex(".1_5"), float_tok("0.15"));
    }

    #[test]
    fn test_leading_dot_float_with_exponent() {
        // The fraction-then-exponent path is shared with the digit-dot float.
        assert_eq!(lex(".25e3"), float_tok("0.25e3"));
        assert_eq!(lex(".5E-2"), float_tok("0.5E-2"));
        assert_eq!(lex(".5e+10"), float_tok("0.5e+10"));
    }

    #[test]
    fn test_leading_dot_float_after_whitespace_or_delimiter() {
        // A `.` at a token boundary (after whitespace, after `(`) is a float.
        assert_eq!(
            lex("f .5"),
            vec![
                TokenKind::Ident("f".to_string()),
                TokenKind::FloatLit("0.5".to_string())
            ]
        );
        assert_eq!(
            lex("(.5)"),
            vec![
                TokenKind::LParen,
                TokenKind::FloatLit("0.5".to_string()),
                TokenKind::RParen
            ]
        );
    }

    #[test]
    fn test_dot_after_ident_stays_projection_not_float() {
        // `x.5` is glued to `x` (no whitespace), so `.5` is NOT a leading-dot
        // float: it stays `Ident(x)`, `Dot`, `NatLit(5)` (projection-or-error
        // as decided later by the parser), exactly as before this feature.
        assert_eq!(
            lex("x.5"),
            vec![
                TokenKind::Ident("x".to_string()),
                TokenKind::Dot,
                TokenKind::nat_lit(5)
            ]
        );
        // Likewise after a closing paren: `(x).5` is projection territory.
        assert_eq!(
            lex(").5"),
            vec![TokenKind::RParen, TokenKind::Dot, TokenKind::nat_lit(5)]
        );
    }

    #[test]
    fn test_digit_dot_digit_unaffected_by_leading_dot_path() {
        // `1.5` remains a single float; the `.` is consumed inside lex_number
        // and never reaches the leading-dot dispatch.
        assert_eq!(lex("1.5"), float_tok("1.5"));
    }

    #[test]
    fn test_range_operator_unaffected_by_leading_dot_path() {
        // `1..2` is still two nats around a `DotDot`; `..` never starts a float.
        assert_eq!(
            lex("1..2"),
            vec![
                TokenKind::nat_lit(1),
                TokenKind::DotDot,
                TokenKind::nat_lit(2)
            ]
        );
        // A standalone `..` (range) followed by digits is DotDot then a nat,
        // because the first `.` is followed by `.`, not a digit.
        assert_eq!(lex("..2"), vec![TokenKind::DotDot, TokenKind::nat_lit(2)]);
    }

    #[test]
    fn test_bare_dot_operator_unaffected() {
        // A `.` not followed by a digit is still the bare Dot operator.
        assert_eq!(
            lex(".foo"),
            vec![TokenKind::Dot, TokenKind::Ident("foo".to_string())]
        );
    }

    #[test]
    fn test_hex_literal_is_never_float() {
        // Radix-prefixed literals never take the float path, even before a dot.
        assert_eq!(lex("0xFF"), vec![TokenKind::nat_lit(255)]);
        assert_eq!(
            lex("0xFF.0"),
            vec![
                TokenKind::nat_lit(255),
                TokenKind::Dot,
                TokenKind::nat_lit(0)
            ]
        );
    }

    #[test]
    fn test_bare_exponent_letter_is_not_float() {
        // `1e` with no following digit is `1` then identifier `e`, not a float.
        assert_eq!(
            lex("1e"),
            vec![TokenKind::nat_lit(1), TokenKind::Ident("e".to_string())]
        );
    }

    #[test]
    fn test_char_simple() {
        assert_eq!(lex("'a'"), vec![TokenKind::CharLit('a')]);
        assert_eq!(lex("'Z'"), vec![TokenKind::CharLit('Z')]);
        assert_eq!(lex("'0'"), vec![TokenKind::CharLit('0')]);
        assert_eq!(lex("' '"), vec![TokenKind::CharLit(' ')]);
    }

    #[test]
    fn test_char_escapes() {
        assert_eq!(lex(r"'\n'"), vec![TokenKind::CharLit('\n')]);
        assert_eq!(lex(r"'\t'"), vec![TokenKind::CharLit('\t')]);
        assert_eq!(lex(r"'\\'"), vec![TokenKind::CharLit('\\')]);
        assert_eq!(lex(r"'\''"), vec![TokenKind::CharLit('\'')]);
        assert_eq!(lex(r"'\0'"), vec![TokenKind::CharLit('\0')]);
    }

    #[test]
    fn test_char_unicode_escape() {
        // `\u{...}` braces around hex digits.
        assert_eq!(lex(r"'\u{41}'"), vec![TokenKind::CharLit('A')]);
        assert_eq!(lex(r"'\u{1F600}'"), vec![TokenKind::CharLit('\u{1F600}')]);
        // `\xHH` two-digit hex escape.
        assert_eq!(lex(r"'\x41'"), vec![TokenKind::CharLit('A')]);
    }

    #[test]
    fn test_char_unterminated_is_error() {
        // Missing closing quote at end of input.
        assert_eq!(
            lex("'a"),
            vec![TokenKind::Error(LexError::UnterminatedChar)]
        );
        // A lone `'` at end of input.
        assert_eq!(lex("'"), vec![TokenKind::Error(LexError::UnterminatedChar)]);
    }

    #[test]
    fn test_char_empty_and_multi_are_error() {
        // `''` has no character; `'ab'` has too many.
        assert_eq!(lex("''"), vec![TokenKind::Error(LexError::InvalidChar)]);
        assert_eq!(lex("'ab'"), vec![TokenKind::Error(LexError::InvalidChar)]);
    }

    #[test]
    fn test_trailing_prime_in_ident_is_not_char() {
        // A trailing prime stays part of the identifier; only a *leading* `'`
        // begins a char literal.
        assert_eq!(lex("x'"), vec![TokenKind::Ident("x'".to_string())]);
        assert_eq!(lex("foo''"), vec![TokenKind::Ident("foo''".to_string())]);
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            lex("\"hello\""),
            vec![TokenKind::StringLit("hello".to_string())]
        );
        assert_eq!(
            lex("\"hello\\nworld\""),
            vec![TokenKind::StringLit("hello\nworld".to_string())]
        );
    }

    #[test]
    fn test_string_hex_escape_resolves_to_char() {
        // `\xHH` decodes exactly two hex digits into the string buffer.
        assert_eq!(
            lex(r#""\x41""#),
            vec![TokenKind::StringLit("A".to_string())]
        );
        assert_eq!(
            lex(r#""a\x42c""#),
            vec![TokenKind::StringLit("aBc".to_string())]
        );
    }

    #[test]
    fn test_string_unicode_escape_resolves_to_char() {
        // `\u{...}` decodes one or more hex digits, including astral scalars.
        assert_eq!(
            lex(r#""\u{41}""#),
            vec![TokenKind::StringLit("A".to_string())]
        );
        assert_eq!(
            lex(r#""grin: \u{1F600}""#),
            vec![TokenKind::StringLit("grin: \u{1F600}".to_string())]
        );
    }

    #[test]
    fn test_string_nul_escape_resolves_to_char() {
        // `\0` is a NUL scalar in strings, matching char literals.
        assert_eq!(
            lex(r#""a\0b""#),
            vec![TokenKind::StringLit("a\0b".to_string())]
        );
    }

    #[test]
    fn test_string_malformed_hex_escape_is_error() {
        // `\xGG` has no hex digit; the malformed escape yields the same typed
        // error as char literals. The lexer recovers and keeps tokenizing the
        // remainder, so only the first (error) token is asserted here.
        assert_eq!(
            lex(r#""\xGG""#).first(),
            Some(&TokenKind::Error(LexError::InvalidUnicodeEscape))
        );
        // A single hex digit then a non-hex char is still malformed.
        assert_eq!(
            lex(r#""\x4Z""#).first(),
            Some(&TokenKind::Error(LexError::InvalidUnicodeEscape))
        );
    }

    #[test]
    fn test_string_unknown_escape_is_error() {
        // An unrecognized escape character is rejected with its own variant
        // (matching char-literal behavior); recovery continues afterwards.
        assert_eq!(
            lex(r#""\q""#).first(),
            Some(&TokenKind::Error(LexError::UnknownEscapeSequence('q')))
        );
    }

    #[test]
    fn test_string_escape_truncated_by_eof_is_unterminated_string() {
        // An escape cut off by end-of-input reports `UnterminatedString`,
        // distinct from the char literal's `UnterminatedChar`.
        assert_eq!(
            lex(r#""abc\"#),
            vec![TokenKind::Error(LexError::UnterminatedString)]
        );
        // A `\u{...}` missing its closing brace at EOF is also unterminated.
        assert_eq!(
            lex(r#""\u{41"#),
            vec![TokenKind::Error(LexError::UnterminatedString)]
        );
    }

    #[test]
    fn test_string_simple_escapes_unchanged() {
        // The original simple escapes still resolve as before.
        assert_eq!(
            lex(r#""\t\r\\\"""#),
            vec![TokenKind::StringLit("\t\r\\\"".to_string())]
        );
    }

    #[test]
    fn test_string_gap_elides_newline_and_leading_whitespace() {
        // Lean 4 string gap: `\` + newline + leading indentation is elided so
        // the literal continues on the next source line. `"abc\<NL>   def"`
        // therefore denotes the single string `abcdef`.
        assert_eq!(
            lex("\"abc\\\n   def\""),
            vec![TokenKind::StringLit("abcdef".to_string())]
        );
    }

    #[test]
    fn test_string_gap_consumes_whitespace_around_the_newline() {
        // Whitespace before the newline (trailing spaces/tabs) and after it is
        // all elided; the gap must still contain exactly one newline.
        assert_eq!(
            lex("\"abc\\  \t\n\t  def\""),
            vec![TokenKind::StringLit("abcdef".to_string())]
        );
    }

    #[test]
    fn test_string_gap_multiple_gaps_in_one_literal() {
        // Several gaps may appear in one literal, each eliding its own newline.
        assert_eq!(
            lex("\"a\\\n b\\\n c\""),
            vec![TokenKind::StringLit("abc".to_string())]
        );
    }

    #[test]
    fn test_string_gap_at_start_of_literal() {
        // A gap immediately after the opening quote elides leading layout.
        assert_eq!(
            lex("\"\\\n  hi\""),
            vec![TokenKind::StringLit("hi".to_string())]
        );
    }

    #[test]
    fn test_string_gap_does_not_disturb_regular_escapes() {
        // `\n` is still a literal newline escape, distinct from a string gap
        // (which requires the backslash to be followed by real whitespace).
        assert_eq!(
            lex("\"a\\nb\""),
            vec![TokenKind::StringLit("a\nb".to_string())]
        );
    }

    #[test]
    fn test_string_gap_without_newline_is_error() {
        // `\` + whitespace that never reaches a newline before a non-whitespace
        // character is a malformed gap (upstream: "expecting newline").
        assert_eq!(
            lex("\"a\\ b\"").first(),
            Some(&TokenKind::Error(LexError::InvalidStringGap))
        );
    }

    #[test]
    fn test_string_gap_with_two_newlines_is_error() {
        // A gap may contain at most one newline; a second is rejected
        // (upstream: "unexpected additional newline in string gap").
        assert_eq!(
            lex("\"a\\\n\n b\"").first(),
            Some(&TokenKind::Error(LexError::InvalidStringGap))
        );
    }

    #[test]
    fn test_string_gap_unterminated_is_unterminated_string() {
        // Whitespace (incl. a newline) after `\` that runs into end-of-input
        // before any closing quote is reported as an unterminated string.
        assert_eq!(
            lex("\"a\\\n   ").first(),
            Some(&TokenKind::Error(LexError::UnterminatedString))
        );
    }

    #[test]
    fn test_raw_string_no_hashes_basic() {
        // `r"hello"` is a plain raw string equal to `hello` at the surface.
        assert_eq!(
            lex("r\"hello\""),
            vec![TokenKind::StringLit("hello".to_string())]
        );
    }

    #[test]
    fn test_raw_string_backslash_n_stays_two_literal_chars() {
        // In a raw string `\n` is a backslash followed by `n`, NOT a newline.
        // The Rust source `r#"r"\n""#` is the four characters: r " \ n ".
        assert_eq!(
            lex(r#"r"\n""#),
            vec![TokenKind::StringLit("\\n".to_string())]
        );
        // And the contents really differ from the escaped string form.
        assert_ne!(
            lex(r#"r"\n""#),
            vec![TokenKind::StringLit("\n".to_string())]
        );
    }

    #[test]
    fn test_raw_string_backslash_is_literal() {
        // A lone backslash and a backslash-quote are both literal in raw form.
        assert_eq!(
            lex(r#"r"a\b\\c""#),
            vec![TokenKind::StringLit("a\\b\\\\c".to_string())]
        );
    }

    #[test]
    fn test_raw_string_hash_form_embeds_quotes() {
        // `r#"say "hi""#` embeds interior double quotes; the literal closes only
        // at `"#`. Built from a raw Rust literal to keep the bytes explicit.
        assert_eq!(
            lex(r##"r#"say "hi""#"##),
            vec![TokenKind::StringLit("say \"hi\"".to_string())]
        );
    }

    #[test]
    fn test_raw_string_multi_hash_form() {
        // With two hashes, a `"#` inside is content; only `"##` terminates.
        assert_eq!(
            lex(r###"r##"a "# b"##"###),
            vec![TokenKind::StringLit("a \"# b".to_string())]
        );
    }

    #[test]
    fn test_raw_string_hash_form_trailing_quote_in_content() {
        // A quote immediately before the real terminator is content: the
        // sequence `""#` in `r#"x""#` is a literal `"` then the closing `"#`.
        assert_eq!(
            lex(r##"r#"x""#"##),
            vec![TokenKind::StringLit("x\"".to_string())]
        );
    }

    #[test]
    fn test_raw_string_no_hash_stops_at_first_quote() {
        // Without hashes the first interior `"` ends the raw string, so the
        // remainder lexes as a separate identifier.
        assert_eq!(
            lex("r\"ab\"cd"),
            vec![
                TokenKind::StringLit("ab".to_string()),
                TokenKind::Ident("cd".to_string()),
            ]
        );
    }

    #[test]
    fn test_raw_string_unterminated_is_error() {
        // No closing quote at all.
        assert_eq!(
            lex("r\"abc"),
            vec![TokenKind::Error(LexError::UnterminatedString)]
        );
        // Hash form whose closing `"#` never appears.
        assert_eq!(
            lex(r##"r#"abc"##).first(),
            Some(&TokenKind::Error(LexError::UnterminatedString))
        );
        // Closing quote present but with too few trailing hashes.
        assert_eq!(
            lex(r###"r##"abc"#"###).first(),
            Some(&TokenKind::Error(LexError::UnterminatedString))
        );
    }

    #[test]
    fn test_raw_string_prefix_r_alone_is_ident() {
        // A bare `r` with no following quote/hash stays an identifier.
        assert_eq!(lex("r"), vec![TokenKind::Ident("r".to_string())]);
    }

    #[test]
    fn test_raw_string_prefix_rabbit_is_ident() {
        // `rabbit` starts with `r` but is an ordinary identifier, not a raw
        // string (no `"` or `#"` immediately follows the `r`).
        assert_eq!(lex("rabbit"), vec![TokenKind::Ident("rabbit".to_string())]);
        // `rhash` (r then identifier char) likewise stays an identifier.
        assert_eq!(lex("rhash"), vec![TokenKind::Ident("rhash".to_string())]);
    }

    #[test]
    fn test_raw_string_r_followed_by_hash_then_ident_is_ident_and_hash() {
        // `r#x`: the `#` is not followed by `"`, so this is NOT a raw string.
        // It lexes as ident `r`, a `Hash` token, then ident `x`.
        assert_eq!(
            lex("r#x"),
            vec![
                TokenKind::Ident("r".to_string()),
                TokenKind::Hash,
                TokenKind::Ident("x".to_string()),
            ]
        );
    }

    #[test]
    fn test_normal_string_still_lexes_with_escapes() {
        // The non-raw path is untouched: `"\n"` is still a single newline.
        assert_eq!(lex("\"\\n\""), vec![TokenKind::StringLit("\n".to_string())]);
    }

    #[test]
    fn test_raw_string_empty() {
        // `r""` and `r#""#` are both the empty string.
        assert_eq!(lex("r\"\""), vec![TokenKind::StringLit(String::new())]);
        assert_eq!(lex(r##"r#""#"##), vec![TokenKind::StringLit(String::new())]);
    }

    #[test]
    fn test_interpolated_string_s_prefix() {
        assert_eq!(
            lex("s!\"hello {name}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                "hello {name}".to_string()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_m_prefix() {
        assert_eq!(
            lex("m!\"error: {msg}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::MessageData,
                "error: {msg}".to_string()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_f_prefix() {
        assert_eq!(
            lex("f!\"x = {x}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::Format,
                "x = {x}".to_string()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_plain_text() {
        assert_eq!(
            lex("s!\"no interpolation\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                "no interpolation".to_string()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_nested_braces() {
        // Nested braces inside interpolation: s!"{f {x}}"
        assert_eq!(
            lex("s!\"{f {x}}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                "{f {x}}".to_string()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_escaped_content() {
        // Escaped braces preserved verbatim for parse_interpolation
        assert_eq!(
            lex("s!\"\\{literal\\}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                "\\{literal\\}".to_string()
            )]
        );
    }

    #[test]
    fn test_s_bang_without_quote_is_ident() {
        // s! not followed by " should be a regular identifier
        assert_eq!(lex("s!"), vec![TokenKind::Ident("s!".to_string())]);
    }

    #[test]
    fn test_interpolated_string_empty() {
        // s!"" produces an empty interpolated string
        assert_eq!(
            lex("s!\"\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                String::new()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_multiple_exprs() {
        // s!"{x} and {y}" preserves multiple brace-delimited segments
        assert_eq!(
            lex("s!\"{x} and {y}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                "{x} and {y}".to_string()
            )]
        );
    }

    #[test]
    fn test_interpolated_string_only_expr() {
        // s!"{42}" — just an expression, no literal text
        assert_eq!(
            lex("s!\"{42}\""),
            vec![TokenKind::InterpolatedString(
                InterpolatedStringKind::String,
                "{42}".to_string()
            )]
        );
    }

    #[test]
    fn test_operators() {
        assert_eq!(lex("->"), vec![TokenKind::Arrow]);
        assert_eq!(lex("→"), vec![TokenKind::Arrow]);
        assert_eq!(lex("=>"), vec![TokenKind::FatArrow]);
        assert_eq!(lex(":="), vec![TokenKind::ColonEq]);
        assert_eq!(lex("λ"), vec![TokenKind::Lambda]);
        assert_eq!(lex("∀"), vec![TokenKind::Forall]);
        assert_eq!(lex("<;>"), vec![TokenKind::SeqFocusOp]);
        assert_eq!(lex("|-"), vec![TokenKind::Turnstile]);
        assert_eq!(lex("⊢"), vec![TokenKind::Turnstile]);
        // Forward pipe `|>` is its own token; `|>.` is `ForwardPipe` + `Dot`.
        assert_eq!(lex("|>"), vec![TokenKind::ForwardPipe]);
        assert_eq!(lex("|>."), vec![TokenKind::ForwardPipe, TokenKind::Dot]);
        assert_eq!(lex("<|"), vec![TokenKind::BackwardPipe]);
    }

    #[test]
    fn test_mapsto_unicode() {
        // Unicode mapsto (U+21A6) is an alias for fat arrow in Lean 4 lambda syntax
        assert_eq!(lex("↦"), vec![TokenKind::FatArrow]);
        // Used in lambda expressions: fun x ↦ x + 1
        assert_eq!(
            lex("fun x ↦ x"),
            vec![
                TokenKind::Fun,
                TokenKind::Ident("x".to_string()),
                TokenKind::FatArrow,
                TokenKind::Ident("x".to_string()),
            ]
        );
    }

    #[test]
    fn test_set_difference_backslash() {
        assert_eq!(lex("\\"), vec![TokenKind::SDiff]);
        assert_eq!(
            lex("S \\ T"),
            vec![
                TokenKind::Ident("S".to_string()),
                TokenKind::SDiff,
                TokenKind::Ident("T".to_string()),
            ]
        );
    }

    #[test]
    fn test_mathlib_ring_operators() {
        // Mathlib compound operators for ring/algebra morphisms
        // ≃+* (RingEquiv) - ring isomorphism
        assert_eq!(lex("≃+*"), vec![TokenKind::Ident("RingEquiv".to_string())]);
        // ≃* (MulEquiv) - multiplicative group isomorphism
        assert_eq!(lex("≃*"), vec![TokenKind::Ident("MulEquiv".to_string())]);
        // →+* (RingHom) - ring homomorphism
        assert_eq!(lex("→+*"), vec![TokenKind::Ident("RingHom".to_string())]);
        // Plain ≃ should still work
        assert_eq!(lex("≃"), vec![TokenKind::Equiv]);
        // Plain → should still work
        assert_eq!(lex("→"), vec![TokenKind::Arrow]);
        // ≃+ should be ≃ followed by + (not a compound)
        assert_eq!(lex("≃+"), vec![TokenKind::Equiv, TokenKind::Plus]);
        // →+ should be → followed by + (not a compound)
        assert_eq!(lex("→+"), vec![TokenKind::Arrow, TokenKind::Plus]);
    }

    #[test]
    fn test_exists_unique() {
        // ∃! (unique existence)
        assert_eq!(lex("∃!"), vec![TokenKind::ExistsUnique]);
        // ∃ alone
        assert_eq!(lex("∃"), vec![TokenKind::Exists]);
        // ∃! in context
        assert_eq!(
            lex("∃! x,"),
            vec![
                TokenKind::ExistsUnique,
                TokenKind::Ident("x".to_string()),
                TokenKind::Comma,
            ]
        );
    }

    #[test]
    fn test_pnat_notation() {
        // ℕ+ is PNat (positive naturals) in Mathlib
        assert_eq!(lex("ℕ+"), vec![TokenKind::Ident("PNat".to_string())]);
        // ℤ+ is Int.Positive in Mathlib
        assert_eq!(
            lex("ℤ+"),
            vec![TokenKind::Ident("Int.Positive".to_string())]
        );
        // Plain ℕ and ℤ should still work
        assert_eq!(lex("ℕ"), vec![TokenKind::Ident("Nat".to_string())]);
        assert_eq!(lex("ℤ"), vec![TokenKind::Ident("Int".to_string())]);
        // ℕ + x should be Nat followed by Plus (not PNat)
        assert_eq!(
            lex("ℕ + x"),
            vec![
                TokenKind::Ident("Nat".to_string()),
                TokenKind::Plus,
                TokenKind::Ident("x".to_string()),
            ]
        );
        // ℕ+ in context (FATE-X file 94 pattern)
        assert_eq!(
            lex("(d : ℕ+)"),
            vec![
                TokenKind::LParen,
                TokenKind::Ident("d".to_string()),
                TokenKind::Colon,
                TokenKind::Ident("PNat".to_string()),
                TokenKind::RParen,
            ]
        );
    }

    #[test]
    fn test_angle_symbol() {
        // ∠ (U+2220) is angle notation in geometry - maps to "angle" identifier
        assert_eq!(lex("∠"), vec![TokenKind::Ident("angle".to_string())]);
        // In context: ∠ A B C should parse as angle function applied to A, B, C
        assert_eq!(
            lex("∠ A B C"),
            vec![
                TokenKind::Ident("angle".to_string()),
                TokenKind::Ident("A".to_string()),
                TokenKind::Ident("B".to_string()),
                TokenKind::Ident("C".to_string()),
            ]
        );
    }

    #[test]
    fn test_delimiters() {
        assert_eq!(
            lex("(){}[]"),
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
            ]
        );
    }

    #[test]
    fn test_complex() {
        let tokens = lex("def id (x : Type) := x");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Def,
                TokenKind::Ident("id".to_string()),
                TokenKind::LParen,
                TokenKind::Ident("x".to_string()),
                TokenKind::Colon,
                TokenKind::Type,
                TokenKind::RParen,
                TokenKind::ColonEq,
                TokenKind::Ident("x".to_string()),
            ]
        );
    }

    #[test]
    fn test_lambda() {
        let tokens = lex("fun x => x");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Fun,
                TokenKind::Ident("x".to_string()),
                TokenKind::FatArrow,
                TokenKind::Ident("x".to_string()),
            ]
        );
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            lex("x -- comment\ny"),
            vec![
                TokenKind::Ident("x".to_string()),
                TokenKind::Ident("y".to_string()),
            ]
        );

        assert_eq!(
            lex("x /- block -/ y"),
            vec![
                TokenKind::Ident("x".to_string()),
                TokenKind::Ident("y".to_string()),
            ]
        );
    }

    #[test]
    fn test_doc_comment_captures_inner_text() {
        let (_tokens, docs) = Lexer::tokenize_with_docs("/-- The identity. -/\ndef f := 1");
        assert_eq!(docs.len(), 1, "expected exactly one captured doc comment");
        assert_eq!(docs[0].text, "The identity.");
    }

    #[test]
    fn test_doc_comment_token_stream_unchanged() {
        // The token vector returned by `tokenize_with_docs` must be identical
        // to `tokenize` — doc comments are skipped as trivia, not emitted.
        let input = "/-- doc -/\ndef f := 1";
        let plain = Lexer::tokenize(input);
        let (with_docs, _) = Lexer::tokenize_with_docs(input);
        let plain_kinds: Vec<_> = plain.iter().map(|t| &t.kind).collect();
        let with_docs_kinds: Vec<_> = with_docs.iter().map(|t| &t.kind).collect();
        assert_eq!(plain_kinds, with_docs_kinds);
    }

    #[test]
    fn test_ordinary_block_comment_not_captured_as_doc() {
        let (_tokens, docs) = Lexer::tokenize_with_docs("/- not a doc -/\ndef f := 1");
        assert!(docs.is_empty(), "ordinary block comment must not be a doc");
    }

    #[test]
    fn test_nested_block_comment_not_captured_and_skipped() {
        // Nested `/- /- -/ -/` must still be skipped correctly and not yield a
        // doc comment.
        let input = "/- outer /- inner -/ -/\ndef f := 1";
        let (tokens, docs) = Lexer::tokenize_with_docs(input);
        assert!(docs.is_empty(), "nested block comment must not be a doc");
        // The comment is fully skipped: first real token is `def`.
        assert_eq!(tokens.first().map(|t| &t.kind), Some(&TokenKind::Def));
    }

    #[test]
    fn test_doc_comment_with_nested_block_inside() {
        // A doc comment that itself contains a nested `/- -/` pair captures the
        // inner text (including the nested delimiters) and tracks depth so the
        // first `-/` does not prematurely close it.
        let (_tokens, docs) = Lexer::tokenize_with_docs("/-- a /- b -/ c -/\ndef f := 1");
        assert_eq!(docs.len(), 1);
        assert_eq!(docs[0].text, "a /- b -/ c");
    }

    #[test]
    fn test_module_doc_comment_not_captured() {
        // `/-! ... -/` is a module/section doc, not a declaration doc; it must
        // be skipped without being captured.
        let (_tokens, docs) = Lexer::tokenize_with_docs("/-! module doc -/\ndef f := 1");
        assert!(docs.is_empty(), "module doc `/-!` must not be captured");
    }

    #[test]
    fn test_no_doc_comment_yields_none() {
        let (_tokens, docs) = Lexer::tokenize_with_docs("def f := 1");
        assert!(docs.is_empty(), "decl with no doc must capture nothing");
    }

    #[test]
    fn test_whitespace() {
        assert_eq!(
            lex("  x  y  "),
            vec![
                TokenKind::Ident("x".to_string()),
                TokenKind::Ident("y".to_string()),
            ]
        );
    }

    // =========================================================================
    // Property-based tests (#175)
    // =========================================================================

    use proptest::prelude::*;

    proptest! {
        /// Lexer never panics on arbitrary input
        #[test]
        fn prop_lexer_no_panic(input in "\\PC*") {
            // The lexer should handle any input without panicking
            let _ = Lexer::tokenize(&input);
        }

        /// Token spans are within input bounds
        #[test]
        fn prop_token_spans_valid(input in "[a-zA-Z0-9_+\\-*/=<>(){}\\[\\]:., \\t\\n]*") {
            let tokens = Lexer::tokenize(&input);
            for token in tokens {
                prop_assert!(
                    token.span.start <= input.len(),
                    "Token start {} exceeds input len {} for {:?}",
                    token.span.start, input.len(), token.kind
                );
                prop_assert!(
                    token.span.end <= input.len(),
                    "Token end {} exceeds input len {} for {:?}",
                    token.span.end, input.len(), token.kind
                );
                prop_assert!(
                    token.span.start <= token.span.end,
                    "Token span inverted: {} > {} for {:?}",
                    token.span.start, token.span.end, token.kind
                );
            }
        }

        /// Identifiers lex to themselves
        #[test]
        fn prop_identifier_roundtrip(name in "[a-zA-Z_][a-zA-Z0-9_'?!]*") {
            let tokens = Lexer::tokenize(&name);
            // Filter out EOF
            let non_eof: Vec<_> = tokens.into_iter()
                .filter(|t| t.kind != TokenKind::Eof)
                .collect();

            // Should be exactly one token (unless it's a keyword)
            prop_assert!(
                non_eof.len() == 1,
                "Expected 1 token for '{}', got {:?}",
                name, non_eof
            );

            // Keywords are fine - they take precedence over identifiers
            if let TokenKind::Ident(s) = &non_eof[0].kind {
                prop_assert_eq!(s, &name, "Identifier roundtrip failed");
            }
        }

        /// Natural number literals preserve value
        #[test]
        fn prop_natlit_value(n in 0u64..u64::MAX/2) {
            let input = n.to_string();
            let tokens = Lexer::tokenize(&input);
            let non_eof: Vec<_> = tokens.into_iter()
                .filter(|t| t.kind != TokenKind::Eof)
                .collect();

            prop_assert!(
                non_eof.len() == 1,
                "Expected 1 token for '{}', got {:?}",
                input, non_eof
            );

            match &non_eof[0].kind {
                TokenKind::NatLit(v) => {
                    prop_assert_eq!(v.to_u64(), Some(n), "NatLit value mismatch");
                }
                other => prop_assert!(false, "Expected NatLit, got {:?}", other),
            }
        }

        /// Unicode arrow equivalence
        #[test]
        fn prop_arrow_unicode_equiv(prefix in "[a-z]{0,5}", suffix in "[a-z]{0,5}") {
            let ascii = format!("{prefix} -> {suffix}");
            let unicode = format!("{prefix} → {suffix}");

            let ascii_tokens = Lexer::tokenize(&ascii);
            let unicode_tokens = Lexer::tokenize(&unicode);

            // Extract just the kinds (ignore spans which will differ)
            let ascii_kinds: Vec<_> = ascii_tokens.iter().map(|t| &t.kind).collect();
            let unicode_kinds: Vec<_> = unicode_tokens.iter().map(|t| &t.kind).collect();

            prop_assert_eq!(
                ascii_kinds, unicode_kinds,
                "Arrow equivalence failed for '{}' vs '{}'",
                ascii, unicode
            );
        }
    }
}
