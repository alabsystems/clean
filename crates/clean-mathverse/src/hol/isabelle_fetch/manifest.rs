// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pinned manifest of the Isabelle import's public inputs
//! (`data/isabelle_public_inputs.json`).
//!
//! The committed file is compiled into the binary, so the command checks the
//! same pins wherever it runs; `--manifest <path>` reads another file instead.
//! Every value is validated on load: a checksum that is not 64 lowercase hex
//! digits, a commit that is not 40, a file name that is not a single path
//! component, or an id that appears twice is an error, never a guess.

use std::collections::BTreeSet;
use std::path::{Component, Path};

use serde::Deserialize;

use super::error::FetchError;

/// The committed manifest, relative to the repository root.
pub(crate) const MANIFEST_REL_PATH: &str = "data/isabelle_public_inputs.json";

/// The manifest schema version this code reads.
pub(crate) const MANIFEST_VERSION: u32 = 1;

/// The committed manifest's text, compiled in.
pub(super) const EMBEDDED_MANIFEST: &str =
    include_str!("../../../../../data/isabelle_public_inputs.json");

/// The whole manifest.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct PublicInputs {
    /// Schema version; must equal [`MANIFEST_VERSION`].
    pub(crate) version: u32,
    /// The date the pins were recorded (`YYYY-MM-DD`).
    pub(crate) recorded: String,
    /// The distribution archives.
    pub(crate) distributions: Vec<Distribution>,
    /// The AFP checkout.
    pub(crate) afp: AfpPin,
    /// What the import needs that this command cannot fetch.
    pub(crate) not_fetched: Vec<NotFetched>,
    /// Where this manifest was read from (not part of the JSON).
    #[serde(skip)]
    pub(crate) origin: String,
}

/// One pinned distribution archive.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Distribution {
    /// The id `--only` selects it by.
    pub(crate) id: String,
    /// The file name inside the work directory.
    pub(crate) file: String,
    /// Where to download it.
    pub(crate) url: String,
    /// Pinned size in bytes.
    pub(crate) bytes: u64,
    /// Pinned sha256, lowercase hex.
    pub(crate) sha256: String,
    /// The release's `ISABELLE_ID`.
    pub(crate) isabelle_id: String,
    /// Which parts of the import used it.
    pub(crate) used_by: String,
}

/// The pinned AFP checkout.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct AfpPin {
    /// The id `--only` selects it by.
    pub(crate) id: String,
    /// The git repository.
    pub(crate) repo: String,
    /// The pinned commit, 40 lowercase hex digits.
    pub(crate) rev: String,
    /// The directory name inside the work directory.
    pub(crate) dir: String,
    /// The fetch depth (1 reproduces the import's shallow clone).
    pub(crate) depth: u32,
    /// The pinned commit's date (`YYYY-MM-DD`).
    pub(crate) commit_date: String,
    /// Which parts of the import used it.
    pub(crate) used_by: String,
    /// The AFP release that matches Isabelle2025-2, recorded as information:
    /// the import did not use it and this command does not fetch it.
    pub(crate) matching_release_not_used: AfpReleaseNote,
}

/// An AFP release recorded for information only.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct AfpReleaseNote {
    /// The git repository.
    pub(crate) repo: String,
    /// The commit observed when the manifest was recorded.
    pub(crate) rev: String,
    /// Why it is recorded.
    pub(crate) note: String,
}

/// Something the import needs that this command cannot fetch.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct NotFetched {
    /// What it is.
    pub(crate) what: String,
    /// Why it cannot be fetched.
    pub(crate) why: String,
    /// How to get it back.
    pub(crate) how_to_get_it: String,
}

impl PublicInputs {
    /// The manifest compiled into this binary.
    ///
    /// # Errors
    /// [`FetchError::ManifestParse`] or [`FetchError::ManifestInvalid`] if the
    /// committed file is malformed (the unit tests rule that out).
    pub(crate) fn embedded() -> Result<Self, FetchError> {
        Self::parse(
            EMBEDDED_MANIFEST,
            &format!("{MANIFEST_REL_PATH} (built in)"),
        )
    }

    /// Read and validate the manifest at `path`.
    ///
    /// # Errors
    /// [`FetchError::ManifestRead`] if it cannot be read; otherwise as
    /// [`PublicInputs::parse`].
    pub(crate) fn load(path: &Path) -> Result<Self, FetchError> {
        let text = std::fs::read_to_string(path).map_err(|source| FetchError::ManifestRead {
            path: path.to_path_buf(),
            source,
        })?;
        Self::parse(&text, &path.display().to_string())
    }

    /// Parse and validate manifest JSON; `origin` names it in errors and in the
    /// report header.
    ///
    /// # Errors
    /// [`FetchError::ManifestParse`] on malformed JSON or an unknown field;
    /// [`FetchError::ManifestInvalid`] when a value fails validation.
    pub(crate) fn parse(text: &str, origin: &str) -> Result<Self, FetchError> {
        let mut inputs: Self =
            serde_json::from_str(text).map_err(|source| FetchError::ManifestParse {
                origin: origin.to_string(),
                source,
            })?;
        inputs.origin = origin.to_string();
        inputs
            .validate()
            .map_err(|reason| FetchError::ManifestInvalid {
                origin: origin.to_string(),
                reason,
            })?;
        Ok(inputs)
    }

    /// Every id `--only` accepts, in manifest order (distributions, then AFP).
    pub(crate) fn ids(&self) -> Vec<&str> {
        self.distributions
            .iter()
            .map(|d| d.id.as_str())
            .chain(std::iter::once(self.afp.id.as_str()))
            .collect()
    }

    fn validate(&self) -> Result<(), String> {
        if self.version != MANIFEST_VERSION {
            return Err(format!(
                "version {} (this binary reads version {MANIFEST_VERSION})",
                self.version
            ));
        }
        check_date("recorded", &self.recorded)?;
        if self.distributions.is_empty() {
            return Err("no distributions".to_string());
        }
        let mut seen = BTreeSet::new();
        for id in self.ids() {
            if id.is_empty() {
                return Err("an input has an empty id".to_string());
            }
            if !seen.insert(id) {
                return Err(format!("id `{id}` appears twice"));
            }
        }
        for d in &self.distributions {
            check_plain_name(&d.id, "file", &d.file)?;
            check_https(&d.id, &d.url)?;
            if d.bytes == 0 {
                return Err(format!("{}: bytes must be > 0", d.id));
            }
            check_hex(&d.id, "sha256", &d.sha256, 64)?;
            check_nonempty(&d.id, "isabelle_id", &d.isabelle_id)?;
            check_nonempty(&d.id, "used_by", &d.used_by)?;
        }
        let afp = &self.afp;
        check_https(&afp.id, &afp.repo)?;
        check_hex(&afp.id, "rev", &afp.rev, 40)?;
        check_plain_name(&afp.id, "dir", &afp.dir)?;
        if afp.depth == 0 {
            return Err(format!("{}: depth must be >= 1", afp.id));
        }
        check_date(&afp.id, &afp.commit_date)?;
        check_nonempty(&afp.id, "used_by", &afp.used_by)?;
        let note = &afp.matching_release_not_used;
        check_https(&afp.id, &note.repo)?;
        check_hex(&afp.id, "matching_release_not_used.rev", &note.rev, 40)?;
        check_nonempty(&afp.id, "matching_release_not_used.note", &note.note)?;
        if self.not_fetched.is_empty() {
            return Err("not_fetched is empty".to_string());
        }
        for (i, n) in self.not_fetched.iter().enumerate() {
            let at = format!("not_fetched[{i}]");
            check_nonempty(&at, "what", &n.what)?;
            check_nonempty(&at, "why", &n.why)?;
            check_nonempty(&at, "how_to_get_it", &n.how_to_get_it)?;
        }
        Ok(())
    }
}

fn check_nonempty(at: &str, field: &str, value: &str) -> Result<(), String> {
    if value.trim().is_empty() {
        return Err(format!("{at}: {field} is empty"));
    }
    Ok(())
}

fn check_hex(at: &str, field: &str, value: &str, len: usize) -> Result<(), String> {
    let ok = value.len() == len
        && value
            .bytes()
            .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    if !ok {
        return Err(format!(
            "{at}: {field} `{value}` is not {len} lowercase hex digits"
        ));
    }
    Ok(())
}

fn check_https(at: &str, url: &str) -> Result<(), String> {
    match url.strip_prefix("https://") {
        Some(rest) if !rest.is_empty() && !url.chars().any(char::is_whitespace) => Ok(()),
        _ => Err(format!("{at}: `{url}` is not an https URL")),
    }
}

/// A file or directory name inside the work directory: one normal path
/// component, so a manifest cannot point the command outside that directory.
fn check_plain_name(at: &str, field: &str, name: &str) -> Result<(), String> {
    let mut parts = Path::new(name).components();
    let plain = matches!(
        (parts.next(), parts.next()),
        (Some(Component::Normal(_)), None)
    ) && !name.contains(['/', '\\']);
    if !plain {
        return Err(format!(
            "{at}: {field} `{name}` must be a single file or directory name"
        ));
    }
    Ok(())
}

fn check_date(at: &str, date: &str) -> Result<(), String> {
    let b = date.as_bytes();
    let ok = b.len() == 10
        && b.iter().enumerate().all(|(i, c)| {
            if i == 4 || i == 7 {
                *c == b'-'
            } else {
                c.is_ascii_digit()
            }
        });
    if !ok {
        return Err(format!("{at}: date `{date}` is not YYYY-MM-DD"));
    }
    Ok(())
}
