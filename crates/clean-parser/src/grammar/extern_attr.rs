// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Parse represented extern entries without dropping a trailing backend.
//! Unsupported source forms refuse rather than becoming a guessed C entry.

use super::Parser;
use crate::lexer::TokenKind;
use crate::{Attribute, ParseError};
use clean_kernel::env::{
    CompilerExternArity, CompilerExternDescriptor, CompilerExternEntry, CompilerExternIncomplete,
    CompilerExternMetadata,
};
use clean_kernel::Name;

impl Parser {
    pub(super) fn extern_attribute(&mut self) -> Result<Attribute, ParseError> {
        let mut entries = Vec::new();
        while !matches!(self.current_kind(), TokenKind::Comma | TokenKind::RBracket) {
            if entries.len() == 64 {
                return Err(self.extern_attribute_error("extern entry bound exceeded"));
            }
            let (backend, symbol) = match self.current_kind().clone() {
                TokenKind::StringLit(symbol) => {
                    self.advance();
                    (Name::from_string("all"), symbol)
                }
                TokenKind::Ident(backend)
                    if !matches!(backend.as_str(), "inline" | "adhoc" | "foreign" | "opaque") =>
                {
                    let backend = self.name_token(&backend)?.into_name();
                    self.advance();
                    let TokenKind::StringLit(symbol) = self.current_kind().clone() else {
                        return Err(self.extern_attribute_error(
                            "extern backend requires its explicit standard symbol",
                        ));
                    };
                    self.advance();
                    (backend, symbol)
                }
                _ => {
                    return Err(self.extern_attribute_error(
                        "unrepresented extern source form; expected a symbol or backend/symbol pair",
                    ));
                }
            };
            if symbol.is_empty() {
                return Err(self.extern_attribute_error("extern standard symbol is empty"));
            }
            entries.push(CompilerExternEntry::Standard { backend, symbol });
        }
        let metadata = if entries.is_empty() {
            CompilerExternMetadata::Incomplete {
                diagnostic: String::new(),
                reason: CompilerExternIncomplete::UnspecifiedSourceBinding,
            }
        } else {
            CompilerExternMetadata::Complete(CompilerExternDescriptor {
                arity: CompilerExternArity::Unspecified,
                entries,
            })
        };
        Ok(Attribute::ExternMetadata(metadata))
    }

    fn extern_attribute_error(&self, message: &str) -> ParseError {
        ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current_span().start,
            message: message.to_owned(),
        }
    }
}

#[cfg(test)]
mod tests;
