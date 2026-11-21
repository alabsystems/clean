// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed reasons a TrustCore receipt is stale, and why the check could not run.

use super::MODULE_TREE_KEY;
use serde::Serialize;
use std::io;

/// One reason a committed TrustCore launch receipt does not describe the
/// current sources. The rendered text is what the local gate prints.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, thiserror::Error)]
#[serde(tag = "kind", rename_all = "kebab-case")]
#[non_exhaustive]
pub enum StalenessFinding {
    #[error("{artifact}: unreadable ({reason})")]
    Unreadable {
        artifact: &'static str,
        reason: String,
    },
    #[error("{artifact}: missing source_sha256 map")]
    MissingPinMap { artifact: &'static str },
    #[error("{artifact}: expected schema_version {expected}")]
    WrongSchema {
        artifact: &'static str,
        expected: &'static str,
    },
    #[error("{artifact}: source_sha256 is missing {input}")]
    MissingPin {
        artifact: &'static str,
        input: &'static str,
    },
    #[error("{artifact}: pins {input} {pinned} but the working tree hashes to {current}")]
    PinMismatch {
        artifact: &'static str,
        input: &'static str,
        pinned: String,
        current: String,
    },
    #[error("{artifact}: source_sha256 is missing the module-tree pin {MODULE_TREE_KEY}")]
    MissingTreePin { artifact: &'static str },
    #[error(
        "{artifact}: pins module-tree digest {pinned} but the working tree hashes to {current}"
    )]
    TreePinMismatch {
        artifact: &'static str,
        pinned: String,
        current: String,
    },
}

/// Why the current input digests could not be computed. No verdict exists
/// without them, so the caller reports the receipts stale.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TrustcoreError {
    #[error("{input}: {source}")]
    Hash {
        input: &'static str,
        #[source]
        source: io::Error,
    },
}
