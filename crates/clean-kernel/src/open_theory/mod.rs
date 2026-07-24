// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory article parsing, translation, and import support.

mod article;
mod import;
mod name;
mod object;
mod parser;
mod term;
#[cfg(test)]
mod tests;
mod translate;
mod ty;
mod vm;
mod vm_ops;
mod vm_stack;
mod vm_support;

pub use article::{OtArticle, OtCommand};
pub use import::{
    import_article, import_article_file, import_article_text, import_article_with_options,
    OtImportOptions, OtImportedArticle,
};
pub use name::OtName;
pub use object::OtObject;
pub use parser::{
    parse_article, parse_article_file, parse_article_file_with_context, parse_article_with_context,
};
pub use term::{OtConstant, OtTerm, OtTheorem, OtVariable};
pub use translate::{
    translate_term, translate_term_with_context, translate_type, translate_type_with_context,
    OtTranslationContext,
};
pub use ty::{OtSymbolId, OtSymbolOrigin, OtType, OtTypeOperator};
pub use vm::OtContext;

pub type Article = OtArticle;
pub type ArticleCommand = OtCommand;
pub type Constant = OtConstant;
pub type Name = OtName;
pub type Object = OtObject;
pub type SymbolId = OtSymbolId;
pub type SymbolOrigin = OtSymbolOrigin;
pub type Term = OtTerm;
pub type Theorem = OtTheorem;
pub type Type = OtType;
pub type TypeOperator = OtTypeOperator;
pub type Variable = OtVariable;

use thiserror::Error;

/// Result type for OpenTheory parsing, translation, and import.
pub type OpenTheoryResult<T> = Result<T, OpenTheoryError>;

/// Errors raised while handling OpenTheory artifacts.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum OpenTheoryError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("line {line}: invalid OpenTheory command `{command}`")]
    InvalidCommand { line: usize, command: String },
    #[error("line {line}: invalid OpenTheory integer literal `{value}`")]
    InvalidInteger { line: usize, value: String },
    #[error("invalid OpenTheory quoted name literal `{value}`")]
    InvalidQuotedName { value: String },
    #[error("line {line}: the `version` command may only appear first")]
    InvalidVersionPosition { line: usize },
    #[error("stack underflow while executing `{command}`")]
    StackUnderflow { command: &'static str },
    #[error("`{command}` expected a {expected}, found {actual}")]
    ExpectedObject {
        command: &'static str,
        expected: &'static str,
        actual: &'static str,
    },
    #[error("dictionary reference `{key}` was not defined")]
    UnknownDictionaryKey { key: i64 },
    #[error("expected a function type, found {ty:?}")]
    ExpectedFunctionType { ty: OtType },
    #[error("type mismatch: expected {expected:?}, found {actual:?}")]
    TypeMismatch { expected: OtType, actual: OtType },
    #[error("`{command}` expects a boolean proposition, found {ty:?}")]
    ExpectedBoolTerm { command: &'static str, ty: OtType },
    #[error("`{command}` expects a global name, found `{name}`")]
    ExpectedGlobalName { command: &'static str, name: OtName },
    #[error("`{command}` expects an equality conclusion")]
    EqualityConclusionExpected { command: &'static str },
    #[error("malformed OpenTheory object for `{command}`: {detail}")]
    MalformedObject {
        command: &'static str,
        detail: String,
    },
    #[error("unbound OpenTheory type variable `{name}`")]
    UnboundTypeVariable { name: OtName },
    #[error("unbound OpenTheory term variable `{name}` with type {ty:?}")]
    UnboundTermVariable { name: OtName, ty: OtType },
    #[error(
        "OpenTheory type operator `{name}` used with conflicting arities {expected} and {actual}"
    )]
    InconsistentTypeOperatorArity {
        name: OtName,
        expected: usize,
        actual: usize,
    },
    #[error("OpenTheory constant `{name}` used with incompatible types {first:?} and {second:?}")]
    InconsistentConstantType {
        name: OtName,
        first: OtType,
        second: OtType,
    },
}
