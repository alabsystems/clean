// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source errors beside declarations that successfully registered in the kernel.
//! A compiler error is not an elaboration or kernel rejection: later commands
//! must still be able to refer to the declaration.

use crate::ElabError;
use clean_parser::Span;

#[derive(Debug, Clone)]
/// An error emitted after the enclosed declaration registered successfully.
pub struct SourceDiagnostic {
    /// The source-level error, independent of the declaration's kernel validity.
    pub error: ElabError,
    /// Original declaration position, including for a member of a nested block.
    pub span: Option<Span>,
}
