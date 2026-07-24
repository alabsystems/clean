// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Coq importer: SerAPI s-expression parsing, CIC declaration
//! extraction, and phased import pipeline for MathComp, Flocq, CompCert,
//! and the Coq standard library.
//!
//! This module extends the basic `.v` source-level importer in [`crate::coq`]
//! and the kernel-level translator in `clean-kernel::coq_import` with
//! library-specific handling for the major Coq ecosystem libraries.
//!
//! ## Architecture
//!
//! ```text
//! .sexp files (SerAPI output)
//!     |
//!     v
//! [sexp_parser] -- parse_sexp_stream() --> Vec<SexpValue>
//!     |
//!     v
//! [cic_extract] -- extract_declarations() --> Vec<CicDeclaration>
//!     |
//!     v
//! [library_config] -- phase filter + axiom profile --> filtered decls
//!     |
//!     v
//! [pipeline] -- run_coq_import() --> (Vec<CicDeclaration>, ImportResult)
//!     |
//!     v
//! coq_shard.rs -- write to .mathverse shard
//! ```

pub mod cic_extract;
pub mod library_config;
pub mod mathcomp_matrix;
pub mod pipeline;
pub mod sexp_parser;
