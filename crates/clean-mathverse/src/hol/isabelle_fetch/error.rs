// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error type for `clean mathverse isabelle-fetch`.

use std::path::PathBuf;

use thiserror::Error;

/// Errors raised while loading the public-inputs manifest, or while fetching
/// and checking one of its inputs.
///
/// The `Afp*` variants and [`FetchError::NotAFile`] are refusals: something
/// already sits where an input belongs and it is not the pinned input, so the
/// command reports it and leaves it exactly as it was.
#[derive(Debug, Error)]
pub(crate) enum FetchError {
    /// Reading a `--manifest` file failed.
    #[error("cannot read manifest {path}: {source}")]
    ManifestRead {
        /// The manifest file.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },

    /// The manifest is not JSON of the expected shape.
    #[error("cannot parse manifest {origin}: {source}")]
    ManifestParse {
        /// Where the manifest came from (a path, or the built-in copy).
        origin: String,
        /// Underlying JSON error.
        #[source]
        source: serde_json::Error,
    },

    /// The manifest parsed but a value is malformed (a checksum that is not
    /// hex, a file name with a path separator, a duplicate id, ...).
    #[error("invalid manifest {origin}: {reason}")]
    ManifestInvalid {
        /// Where the manifest came from.
        origin: String,
        /// What is wrong with it.
        reason: String,
    },

    /// `--only` named an id the manifest does not have.
    #[error("unknown input id `{id}` (the manifest has: {known})")]
    UnknownId {
        /// The id that was asked for.
        id: String,
        /// The ids the manifest does have, comma-separated.
        known: String,
    },

    /// Creating the work directory or a staging directory failed.
    #[error("cannot create directory {path}: {source}")]
    CreateDir {
        /// The directory.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },

    /// Reading, hashing, renaming or removing a file failed.
    #[error("I/O on {path}: {source}")]
    Io {
        /// The file involved.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },

    /// Writing the progress report failed.
    #[error("cannot write the report: {source}")]
    Output {
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },

    /// Something other than a regular file sits where an archive belongs.
    #[error("{path} exists but is not a regular file; left untouched")]
    NotAFile {
        /// The path.
        path: PathBuf,
    },

    /// `curl` or `git` could not be started.
    #[error("cannot run {program}: {source}")]
    Spawn {
        /// The program.
        program: String,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },

    /// `curl` exited unsuccessfully.
    #[error("download of {url} failed ({status}): {detail}")]
    Download {
        /// The URL.
        url: String,
        /// How curl ended (`exit status 22`, ...).
        status: String,
        /// curl's own message, or where it was printed.
        detail: String,
    },

    /// A downloaded file does not match its pin. The download was deleted.
    #[error(
        "{path}: the pin is {expected_bytes} bytes with sha256 {expected_sha256}, \
         the download has {actual}; the download was deleted"
    )]
    Mismatch {
        /// The path the file would have been renamed to.
        path: PathBuf,
        /// Pinned size in bytes.
        expected_bytes: u64,
        /// Pinned sha256, lowercase hex.
        expected_sha256: String,
        /// What the download had instead (`123 bytes` or `sha256 ...`).
        actual: String,
    },

    /// A `git` command failed.
    #[error("git {args} in {dir} failed ({status}): {detail}")]
    Git {
        /// The git arguments, space-joined.
        args: String,
        /// The directory git ran in.
        dir: PathBuf,
        /// How git ended.
        status: String,
        /// git's own message, or where it was printed.
        detail: String,
    },

    /// The AFP directory exists but is not the top of a git checkout.
    #[error("{dir} exists but is not the top of a git checkout; left untouched")]
    AfpNotACheckout {
        /// The AFP directory.
        dir: PathBuf,
    },

    /// The AFP directory is a git checkout with no commit.
    #[error("{dir} is a git checkout with no commit; left untouched")]
    AfpNoHead {
        /// The AFP directory.
        dir: PathBuf,
    },

    /// The AFP directory is checked out at another commit.
    #[error("{dir} is checked out at {head}, not the pinned {rev}; left untouched")]
    AfpOtherRev {
        /// The AFP directory.
        dir: PathBuf,
        /// Its current commit.
        head: String,
        /// The pinned commit.
        rev: String,
    },

    /// The AFP directory is at the pinned commit but tracked files differ
    /// from it.
    #[error("{dir} is at the pinned {rev} but tracked files are modified; left untouched")]
    AfpModified {
        /// The AFP directory.
        dir: PathBuf,
        /// The pinned commit.
        rev: String,
    },

    /// After a fetch, the staging checkout is not at the pinned commit (or
    /// not clean). The staging checkout was deleted.
    #[error(
        "after the fetch {dir} is at {head}, not a clean checkout of the pinned {rev}; \
         the staging checkout was deleted"
    )]
    AfpFetchedWrongRev {
        /// The staging directory.
        dir: PathBuf,
        /// What it held instead.
        head: String,
        /// The pinned commit.
        rev: String,
    },

    /// One or more requested inputs ended FAILED or REFUSED. The per-input
    /// report was printed before this error is returned.
    #[error("{count} requested input(s) could not be verified: {ids}")]
    Unverified {
        /// How many.
        count: usize,
        /// Their ids, comma-separated.
        ids: String,
    },
}
