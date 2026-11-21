// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Coq 8.20 compiled objects and their original kernel terms.
//! Decoding is independent of the corpus importer and does not check a proof.

pub mod constr;
pub mod constr_decode;
pub mod constr_sexp;
pub mod library;
mod local_definition;
pub use local_definition::{read_local_definition, DefinitionBody, LocalDefinition};
pub mod marshal_parser;
mod marshal_reader;
pub mod vo_parser;
