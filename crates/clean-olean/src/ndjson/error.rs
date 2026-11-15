// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Why the NDJSON front door refused or declined an export.
//!
//! Every variant names one rule. [`NdjsonError::exit_class`] splits them the
//! way Lake's external-kernel protocol and the Kernel Arena read an exit code:
//! a malformed export is REJECTED (exit 1), as Lean's `LeanExport` reader
//! rejects it; an export this reader cannot judge -- an unsupported format or
//! Lean version, a resource bound, a limit of Clean's representation (a name,
//! a count, a de Bruijn index) -- is DECLINED (exit 2). A decline never
//! counts as an accept. (A level the reader builds otherwise than Lean reads
//! it is not a reader error: it marks the declarations over it, and the
//! decision declines an export it would otherwise accept, `levels.rs`.)

use thiserror::Error;

/// The verdict class of a run: Lake's and the arena's exit codes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExitClass {
    /// Exit 0: every declaration was replayed and admitted.
    Accept,
    /// Exit 1: the export is malformed, or a declaration was refused.
    Reject,
    /// Exit 2: Clean declines to judge the export.
    Decline,
}

impl ExitClass {
    /// The process exit code: 0, 1 or 2.
    #[must_use]
    pub(crate) fn code(self) -> u8 {
        match self {
            ExitClass::Accept => 0,
            ExitClass::Reject => 1,
            ExitClass::Decline => 2,
        }
    }
}

/// One malformed JSON line, as the strict tokenizer (`json.rs`) refuses it.
///
/// Offsets are byte offsets into the line.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub(crate) enum JsonError {
    /// The line is not UTF-8.
    #[error("offset {offset}: the line is not UTF-8")]
    InvalidUtf8 {
        /// First invalid byte.
        offset: usize,
    },
    /// The line ended inside a value.
    #[error("offset {offset}: unexpected end of input")]
    UnexpectedEnd {
        /// Where the input ended.
        offset: usize,
    },
    /// A byte that cannot start or continue the value being read.
    #[error("offset {offset}: unexpected byte {found:#04x}, expected {expected}")]
    UnexpectedByte {
        /// Where the byte is.
        offset: usize,
        /// The byte.
        found: u8,
        /// What the grammar allows there.
        expected: &'static str,
    },
    /// Bytes after the line's one JSON value (lean4#15542: Lean's reader used
    /// to ignore them).
    #[error("offset {offset}: expected end of input (bytes after the JSON value)")]
    TrailingBytes {
        /// The first byte after the value.
        offset: usize,
    },
    /// An object states one key twice, compared after unescaping
    /// (lean4#15542, lean4#15628).
    #[error("offset {offset}: duplicate object key {key:?}")]
    DuplicateKey {
        /// Where the second occurrence starts.
        offset: usize,
        /// The key, unescaped.
        key: String,
    },
    /// A positive exponent above 100,000 (lean4#15574).
    #[error("offset {offset}: exponent too large (above 100000)")]
    ExponentTooLarge {
        /// Where the number starts.
        offset: usize,
    },
    /// A string escape JSON does not define, or a `\u` surrogate that is not
    /// half of a valid pair (Lean's reader replaces a lone surrogate with
    /// U+FFFD, which can make two distinct names one; this reader refuses it).
    #[error("offset {offset}: invalid string escape")]
    InvalidEscape {
        /// Where the escape starts.
        offset: usize,
    },
    /// A raw control character (below U+0020) inside a string.
    #[error("offset {offset}: unescaped control character in a string")]
    ControlCharacter {
        /// Where the character is.
        offset: usize,
    },
    /// Arrays and objects nested deeper than the reader's bound.
    #[error("offset {offset}: values nested deeper than {limit}")]
    TooDeep {
        /// Where the bound was crossed.
        offset: usize,
        /// The bound.
        limit: usize,
    },
    /// More JSON values on one line than the reader's bound: a line's values
    /// are held in memory at once, so their number is bounded as its bytes are.
    #[error("offset {offset}: more than {limit} JSON values on one line")]
    TooManyValues {
        /// Where the bound was crossed.
        offset: usize,
        /// The bound.
        limit: usize,
    },
}

/// Why the front door refused (exit 1) or declined (exit 2) an export.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub(crate) enum NdjsonError {
    /// The export could not be read.
    #[error("cannot read the export: {0}")]
    Io(String),
    /// The export holds no line at all.
    #[error("the export is empty: it has no `meta` line")]
    Empty,
    /// A line is not one well-formed JSON value.
    #[error("line {line}: invalid JSON: {error}")]
    Json {
        /// 1-based line number.
        line: u64,
        /// The tokenizer's refusal.
        error: JsonError,
    },
    /// A line is longer than the reader's bound.
    #[error("line {line}: longer than {limit} bytes")]
    LineTooLong {
        /// 1-based line number.
        line: u64,
        /// The bound.
        limit: usize,
    },
    /// The first line is not the `meta` object the format requires.
    #[error("line 1: malformed `meta` header: {reason}")]
    MalformedMeta {
        /// What is wrong with it.
        reason: String,
    },
    /// `meta.format.version` is not 3.1 (any patch).
    #[error("format version {version:?} is not supported (this reader reads format 3.1)")]
    FormatVersionUnsupported {
        /// The version the export states.
        version: String,
    },
    /// `meta.lean.version` has no row in the reviewed Lean-world table.
    #[error(
        "Lean version {version:?} has no row in the reviewed table of kernel rule sets \
         (crate::ndjson::world)"
    )]
    LeanVersionUnmapped {
        /// The version the export states.
        version: String,
    },
    /// A line is a JSON value but not an object.
    #[error("line {line}: expected a JSON object")]
    ExpectedObject {
        /// 1-based line number.
        line: u64,
    },
    /// An object whose key set is no record of the format.
    #[error("line {line}: unknown export object with keys {keys:?}")]
    UnknownRecord {
        /// 1-based line number.
        line: u64,
        /// Its keys, in the order written.
        keys: Vec<String>,
    },
    /// A record field is missing, has the wrong JSON type, or is out of range.
    #[error("line {line}: {record}.{field}: {problem}")]
    Field {
        /// 1-based line number.
        line: u64,
        /// The record (`axiom`, `Expr.app`, `InductiveVal`, ...).
        record: &'static str,
        /// The field.
        field: String,
        /// What is wrong with it.
        problem: String,
    },
    /// A field the format allows that Clean cannot represent (an index above
    /// `u64`, a count above `u32`, a de Bruijn index above the kernel's bound):
    /// a limit of this reader, not a finding about the export.
    #[error("line {line}: {record}.{field}: {problem} (a limit of Clean's representation)")]
    RepresentationLimit {
        /// 1-based line number.
        line: u64,
        /// The record.
        record: &'static str,
        /// The field.
        field: String,
        /// What exceeds the limit.
        problem: String,
    },
    /// A record carries a field the format does not define for it.
    #[error("line {line}: {record} has a field the format does not define: {field:?}")]
    UnknownField {
        /// 1-based line number.
        line: u64,
        /// The record.
        record: &'static str,
        /// The field.
        field: String,
    },
    /// A name index is bound twice, index 0 (the anonymous name) included
    /// (lean4#15542).
    #[error("line {line}: Name index {index} bound twice")]
    NameIndexRebound {
        /// 1-based line number.
        line: u64,
        /// The index.
        index: u64,
    },
    /// A level index is bound twice, index 0 (level zero) included
    /// (lean4#15542).
    #[error("line {line}: Level index {index} bound twice")]
    LevelIndexRebound {
        /// 1-based line number.
        line: u64,
        /// The index.
        index: u64,
    },
    /// An expression index is bound twice (lean4#15542).
    #[error("line {line}: Expr index {index} bound twice")]
    ExprIndexRebound {
        /// 1-based line number.
        line: u64,
        /// The index.
        index: u64,
    },
    /// A reference to a name index no earlier line bound.
    #[error("line {line}: Name not found {index}")]
    UnboundName {
        /// 1-based line number.
        line: u64,
        /// The index.
        index: u64,
    },
    /// A reference to a level index no earlier line bound.
    #[error("line {line}: Level not found {index}")]
    UnboundLevel {
        /// 1-based line number.
        line: u64,
        /// The index.
        index: u64,
    },
    /// A reference to an expression index no earlier line bound.
    #[error("line {line}: Expr not found {index}")]
    UnboundExpr {
        /// 1-based line number.
        line: u64,
        /// The index.
        index: u64,
    },
    /// A `natVal` literal longer than the reader's digit budget.
    #[error("line {line}: natVal of {digits} digits exceeds the budget of {limit} digits")]
    NatLiteralBudget {
        /// 1-based line number.
        line: u64,
        /// The literal's length.
        digits: usize,
        /// The budget.
        limit: usize,
    },
    /// A level whose tree (counted with every shared subterm unfolded, as the
    /// kernel's hashing and normalization walk it) is larger than the reader's
    /// budget, or a `const` whose universe levels together are.
    #[error("line {line}: a level tree of {nodes} nodes exceeds the budget of {limit}")]
    LevelBudget {
        /// 1-based line number.
        line: u64,
        /// The (saturating) node count.
        nodes: u64,
        /// The budget.
        limit: u64,
    },
    /// A `max` or `imax` level that no flattened `max` of it may have more
    /// arguments of its own (an `imax`, or a `succ` of one) than
    /// [`super::levels::MAX_LEVEL_COMPOSITE_ARGS`]: the kernel's level
    /// normalization is cubic in them, and it runs on every such record.
    #[error(
        "line {line}: a level `max` of {args} composite arguments (`imax`, or a `succ` of a \
         `max`/`imax`) exceeds the budget of {limit}"
    )]
    LevelArgsBudget {
        /// 1-based line number.
        line: u64,
        /// The composite arguments the record's flattened `max` would have.
        args: u64,
        /// The budget.
        limit: u64,
    },
    /// The export's level records' estimated normalization work exceeds the
    /// reader's per-export budget ([`super::levels::MAX_LEVEL_WORK`]).
    #[error(
        "line {line}: the export's level records reach an estimated {work} units of \
         normalization work, over the budget of {limit} (each `max`/`imax` record costs its \
         tree size times (imax nodes + 1)³)"
    )]
    LevelWorkBudget {
        /// 1-based line number.
        line: u64,
        /// The estimated work so far, this record included.
        work: u64,
        /// The budget.
        limit: u64,
    },
    /// An inductive record that is not one block: a type's or recursor's
    /// `all` other than the record's `types`, a constructor whose `induct` is
    /// not one of them, or the types' `ctors` lists, in order, other than the
    /// record's `ctors`. Lean's replay builds the block from `all`; lean4export
    /// writes `all` = `types`.
    #[error("line {line}: the inductive record is not one block: {problem}")]
    InductiveBlockShape {
        /// 1-based line number.
        line: u64,
        /// What disagrees.
        problem: String,
    },
    /// A stored `isRec` or `isReflexive` other than the value Lean's kernel
    /// computes for the block (`inductive.cpp` `is_rec`/`is_reflexive`), as
    /// far as the record decides it: a nested block's `isReflexive` also
    /// depends on its auxiliary types, so for one the reader refuses only a
    /// stored `false` beside a constructor domain that is a function type into
    /// the block, and the replay compares the rest.
    #[error(
        "line {line}: {name}.{flag} is stored as {stored}, but Lean's kernel computes {kernel} \
         for its block"
    )]
    InductiveFlagMismatch {
        /// 1-based line number.
        line: u64,
        /// The inductive type, rendered unambiguously.
        name: String,
        /// `isRec` or `isReflexive`.
        flag: &'static str,
        /// The stored value.
        stored: bool,
        /// The value Lean's kernel computes.
        kernel: bool,
    },
    /// Two records declare one name (Lean's reader: `Duplicate declaration`).
    #[error("line {line}: Duplicate declaration: {name}")]
    DuplicateDeclaration {
        /// 1-based line number.
        line: u64,
        /// The name, rendered unambiguously.
        name: String,
    },
    /// A record other than `quot` declares one of the names Lean's `quotDecl`
    /// adds (Lean v4.33.1's kernel `check_name`).
    #[error(
        "line {line}: `{name}` is a name of Lean's quotient (`quotDecl`): only a `quot` record \
         may declare it, and this one is {record}"
    )]
    ReservedQuotientName {
        /// 1-based line number.
        line: u64,
        /// The name.
        name: String,
        /// The record that declared it.
        record: &'static str,
    },
    /// A `quot` record whose name is not the one its kind installs.
    #[error("line {line}: quot record of kind {kind} is named `{name}`, not `{expected}`")]
    QuotientNameMismatch {
        /// 1-based line number.
        line: u64,
        /// The kind.
        kind: &'static str,
        /// The name it carries.
        name: String,
        /// The name `quotDecl` installs for that kind.
        expected: &'static str,
    },
    /// A declaration name whose display spelling reads back as another name,
    /// so Clean's replay, which keys declarations by that spelling, cannot
    /// tell it apart (ammkrn/nanoda_lib#37 is the same flattening in nanoda).
    /// The reader stores every name so that it reads back (R118); this is the
    /// check that it did.
    #[error(
        "line {line}: declaration name {name} does not survive Clean's replay labels (it reads \
         back as another name)"
    )]
    UnrepresentableName {
        /// 1-based line number.
        line: u64,
        /// The name, rendered unambiguously.
        name: String,
    },
    /// Two different names the reader stores alike: a string component with
    /// a `.` inside it, or one that reads as a number, is stored escaped
    /// (R118), and another name already spells it that way.
    #[error("line {line}: names {name} and {other} would be stored alike (decision R118)")]
    NameCollision {
        /// 1-based line number.
        line: u64,
        /// The name this line binds, rendered unambiguously.
        name: String,
        /// The name bound before, rendered unambiguously.
        other: String,
    },
}

impl NdjsonError {
    /// Reject (1) or decline (2): see the module documentation.
    #[must_use]
    pub(crate) fn exit_class(&self) -> ExitClass {
        match self {
            NdjsonError::Io(_)
            | NdjsonError::LineTooLong { .. }
            | NdjsonError::FormatVersionUnsupported { .. }
            | NdjsonError::LeanVersionUnmapped { .. }
            | NdjsonError::NatLiteralBudget { .. }
            | NdjsonError::LevelBudget { .. }
            | NdjsonError::LevelArgsBudget { .. }
            | NdjsonError::LevelWorkBudget { .. }
            | NdjsonError::RepresentationLimit { .. }
            | NdjsonError::UnrepresentableName { .. }
            | NdjsonError::NameCollision { .. }
            | NdjsonError::Json {
                error: JsonError::TooDeep { .. } | JsonError::TooManyValues { .. },
                ..
            } => ExitClass::Decline,
            NdjsonError::Empty
            | NdjsonError::Json { .. }
            | NdjsonError::MalformedMeta { .. }
            | NdjsonError::ExpectedObject { .. }
            | NdjsonError::UnknownRecord { .. }
            | NdjsonError::Field { .. }
            | NdjsonError::UnknownField { .. }
            | NdjsonError::NameIndexRebound { .. }
            | NdjsonError::LevelIndexRebound { .. }
            | NdjsonError::ExprIndexRebound { .. }
            | NdjsonError::UnboundName { .. }
            | NdjsonError::UnboundLevel { .. }
            | NdjsonError::UnboundExpr { .. }
            | NdjsonError::DuplicateDeclaration { .. }
            | NdjsonError::InductiveBlockShape { .. }
            | NdjsonError::InductiveFlagMismatch { .. }
            | NdjsonError::ReservedQuotientName { .. }
            | NdjsonError::QuotientNameMismatch { .. } => ExitClass::Reject,
        }
    }

    /// A stable kebab-case name for the rule, for reports and tests.
    #[must_use]
    pub(crate) fn rule(&self) -> &'static str {
        match self {
            NdjsonError::Io(_) => "io",
            NdjsonError::Empty => "empty",
            NdjsonError::Json { error, .. } => match error {
                JsonError::InvalidUtf8 { .. } => "invalid-utf8",
                JsonError::UnexpectedEnd { .. } => "unexpected-end",
                JsonError::UnexpectedByte { .. } => "unexpected-byte",
                JsonError::TrailingBytes { .. } => "trailing-bytes",
                JsonError::DuplicateKey { .. } => "duplicate-key",
                JsonError::ExponentTooLarge { .. } => "exponent-too-large",
                JsonError::InvalidEscape { .. } => "invalid-escape",
                JsonError::ControlCharacter { .. } => "control-character",
                JsonError::TooDeep { .. } => "too-deep",
                JsonError::TooManyValues { .. } => "json-value-budget",
            },
            NdjsonError::LineTooLong { .. } => "line-too-long",
            NdjsonError::MalformedMeta { .. } => "malformed-meta",
            NdjsonError::FormatVersionUnsupported { .. } => "format-version-unsupported",
            NdjsonError::LeanVersionUnmapped { .. } => "lean-version-unmapped",
            NdjsonError::ExpectedObject { .. } => "expected-object",
            NdjsonError::UnknownRecord { .. } => "unknown-record",
            NdjsonError::Field { .. } => "field",
            NdjsonError::UnknownField { .. } => "unknown-field",
            NdjsonError::RepresentationLimit { .. } => "representation-limit",
            NdjsonError::NameIndexRebound { .. } => "name-index-rebound",
            NdjsonError::LevelIndexRebound { .. } => "level-index-rebound",
            NdjsonError::ExprIndexRebound { .. } => "expr-index-rebound",
            NdjsonError::UnboundName { .. } => "unbound-name",
            NdjsonError::UnboundLevel { .. } => "unbound-level",
            NdjsonError::UnboundExpr { .. } => "unbound-expr",
            NdjsonError::NatLiteralBudget { .. } => "nat-literal-budget",
            NdjsonError::LevelBudget { .. } => "level-tree-budget",
            NdjsonError::LevelArgsBudget { .. } => "level-max-args-budget",
            NdjsonError::LevelWorkBudget { .. } => "level-work-budget",
            NdjsonError::InductiveBlockShape { .. } => "inductive-block-shape",
            NdjsonError::InductiveFlagMismatch { .. } => "inductive-flag-mismatch",
            NdjsonError::DuplicateDeclaration { .. } => "duplicate-declaration",
            NdjsonError::ReservedQuotientName { .. } => "reserved-quotient-name",
            NdjsonError::QuotientNameMismatch { .. } => "quotient-name-mismatch",
            NdjsonError::UnrepresentableName { .. } => "unrepresentable-name",
            NdjsonError::NameCollision { .. } => "name-collision",
        }
    }
}
