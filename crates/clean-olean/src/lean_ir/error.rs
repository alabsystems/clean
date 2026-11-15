// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Errors of the compiled-IR decoder. Every one is a refusal: the decoder
//! never skips an object it cannot read, never substitutes a default, and
//! never counts a declaration it did not decode.

use std::path::PathBuf;

use crate::error::OleanError;

/// A failure to decode Lean's compiled IR from a module's files.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum LeanIrError {
    /// The region reader refused (bad header, pointer, bounds, Name, Nat).
    #[error(transparent)]
    Olean(#[from] OleanError),
    /// An object does not have the layout Lean v4.30 gives this IR constructor.
    #[error("{what} at 0x{pointer:x}: {detail}")]
    Layout {
        /// The Lean type being decoded (`FnBody`, `IRType`, …).
        what: &'static str,
        /// The offending object pointer (or tagged scalar).
        pointer: u64,
        /// What was found instead.
        detail: String,
    },
    /// A declaration failed to decode; `source` says where inside it.
    #[error("declaration #{index} ({name}) of {extension}: {source}")]
    InDecl {
        /// Index in the extension's entry array.
        index: usize,
        /// The declaration's name, when its first field decoded.
        name: String,
        /// The extension whose entries were being read.
        extension: &'static str,
        /// The underlying failure.
        #[source]
        source: Box<LeanIrError>,
    },
    /// Nested join points / `case` alternatives exceed the decoder's bound.
    #[error("IR nesting depth exceeds {limit} at 0x{pointer:x}")]
    DepthLimit {
        /// The bound.
        limit: usize,
        /// Where the bound was hit.
        pointer: u64,
    },
    /// The module's `.olean` is not on the search path. Only the census
    /// resolves a module by name, so a build without the `cli` feature never
    /// constructs it.
    #[cfg_attr(not(any(feature = "cli", test)), allow(dead_code))]
    #[error("module {module} not found on the search path ({searched} director(y/ies) tried)")]
    ModuleNotFound {
        /// Module name.
        module: String,
        /// Number of search-path directories tried.
        searched: usize,
    },
    /// A file Lean's import would read is missing or unreadable.
    #[error("module {module}: cannot read {path}: {detail}")]
    MissingFile {
        /// Module name.
        module: String,
        /// The file.
        path: PathBuf,
        /// Why.
        detail: String,
    },
    /// The module's data is inconsistent with how Lean would import it.
    #[error("module {module}: {detail}")]
    Module {
        /// Module name.
        module: String,
        /// What is inconsistent.
        detail: String,
    },
}

impl LeanIrError {
    pub(crate) fn layout(what: &'static str, pointer: u64, detail: impl Into<String>) -> Self {
        LeanIrError::Layout {
            what,
            pointer,
            detail: detail.into(),
        }
    }
}

/// Result alias for the IR decoder.
pub(crate) type LeanIrResult<T> = Result<T, LeanIrError>;
