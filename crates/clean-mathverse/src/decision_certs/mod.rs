// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decision procedure certificate importers for the Mathverse Library (MVP: SAT).
//!
//! Parses DRAT and LRAT proof certificates from SAT solvers and writes them
//! to `.mathverse` shard files with trust tracking and axiom profiles.
//!
//! # Module structure
//!
//! - [`types`]: Core types — `CnfFormula`, `DratStep`, `LratStep`, `SatCertificate`
//! - [`drat`]: DRAT text + binary parser, DIMACS CNF parser
//! - [`lrat`]: LRAT text parser
//! - [`shard_writer`]: Write SAT certificates to `.mathverse` shards

pub mod drat;
pub mod lrat;
pub mod shard_writer;
pub mod types;

// Re-export key types for convenience
pub use drat::{parse_dimacs_cnf, parse_drat_binary, parse_drat_text};
pub use lrat::parse_lrat_text;
pub use shard_writer::{write_sat_certs_to_file, write_sat_certs_to_shard, ShardStats};
pub use types::{
    CertificateVerifyResult, CnfFormula, DratStep, DratStepKind, LratStep, LratStepKind,
    SatCertFormat, SatCertificate, VerifyStats,
};
