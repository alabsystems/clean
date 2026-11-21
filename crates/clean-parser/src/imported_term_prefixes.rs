// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-input syntax contributed by an imported Lean parser descriptor.

use std::collections::HashMap;

use clean_kernel::Name;

use crate::lexer::{Lexer, TokenKind};

/// Registrations for `node kind 1022 (binary andthen (symbol literal) (const num))`.
///
/// The supported literal form is one plain identifier with an adjoining
/// percent sign. The descriptor, syntax-kind Name and import visibility are
/// established by the caller before registration.
#[derive(Debug, Clone, Default)]
pub struct ImportedTermPrefixes {
    kinds: HashMap<String, Name>,
}

/// Why a descriptor cannot be registered in this parse.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ImportedTermPrefixError {
    #[error("imported term prefix requires a nonanonymous syntax kind")]
    AnonymousKind,
    #[error("imported term prefix precedence {0} is unsupported")]
    UnsupportedPrecedence(u32),
    #[error("unsupported imported term prefix {0:?}, expected a plain identifier followed by '%'")]
    UnsupportedLiteral(String),
    #[error("ambiguous imported term prefix {0:?}")]
    Ambiguous(String),
}

impl ImportedTermPrefixes {
    /// Register a decoded numeral-taking prefix. Re-export of an identical
    /// registration is idempotent.
    ///
    /// # Errors
    /// Refuses unsupported literals or precedence and competing syntax kinds
    /// for the same literal.
    pub fn register_numeral_prefix(
        &mut self,
        kind: Name,
        precedence: u32,
        literal: &str,
    ) -> Result<(), ImportedTermPrefixError> {
        if kind.is_anon() {
            return Err(ImportedTermPrefixError::AnonymousKind);
        }
        if precedence != NUMERAL_PREFIX_PRECEDENCE {
            return Err(ImportedTermPrefixError::UnsupportedPrecedence(precedence));
        }
        let literal = literal.trim_ascii();
        let tokens = Lexer::tokenize(literal);
        let [stem, percent, eof] = tokens.as_slice() else {
            return Err(ImportedTermPrefixError::UnsupportedLiteral(literal.into()));
        };
        let TokenKind::Ident(text) = &stem.kind else {
            return Err(ImportedTermPrefixError::UnsupportedLiteral(literal.into()));
        };
        if stem.ident_escaped
            || stem.lean_keyword
            || text.contains('.')
            || stem.span.start != 0
            || !matches!(percent.kind, TokenKind::Percent)
            || percent.span.start != stem.span.end
            || percent.span.end != literal.len()
            || !matches!(eof.kind, TokenKind::Eof)
        {
            return Err(ImportedTermPrefixError::UnsupportedLiteral(literal.into()));
        }
        if let Some(existing) = self.kinds.get(text) {
            return if *existing == kind {
                Ok(())
            } else {
                Err(ImportedTermPrefixError::Ambiguous(literal.into()))
            };
        }
        self.kinds.insert(text.clone(), kind);
        Ok(())
    }

    pub(crate) fn kind(&self, stem: &str) -> Option<&Name> {
        self.kinds.get(stem)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.kinds.is_empty()
    }
}

pub(crate) const NUMERAL_PREFIX_PRECEDENCE: u32 = 1022;
