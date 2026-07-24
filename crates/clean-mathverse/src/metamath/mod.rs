// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metamath `.mm` file importer for the Mathverse Library.
//!
//! Parses Metamath database files (e.g., `set.mm` with ~40K theorems) and
//! writes them to `.mathverse` shards with ZFC axiom profile tagging.
//!
//! Metamath is the simplest formal system to import: its `.mm` format is a
//! plain-text, whitespace-delimited language with a small number of keywords.
//!
//! Reference: <http://us.metamath.org/mpe/mmset.html>

pub mod parser;
pub mod shard_writer;
pub mod types;

#[cfg(test)]
mod tests;
