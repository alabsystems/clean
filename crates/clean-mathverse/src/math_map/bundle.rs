// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bundle-integrity layer: read an untrusted MathMap bundle into memory.
//!
//! A bundle is either a directory or a (optionally zstd-compressed) ustar
//! archive. Every entry path is validated with
//! [`is_safe_relative_path`](super::manifest::is_safe_relative_path) BEFORE it
//! is stored, and the total decoded size is bounded by the policy's
//! `max_bundle_bytes`, so a hostile archive can neither escape the bundle root
//! nor exhaust memory.

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::path::{Component, Path, PathBuf};

use sha2::{Digest, Sha256};

use super::manifest::is_safe_relative_path;

/// An untrusted bundle decoded into memory, keyed by safe relative path.
#[derive(Debug, Clone)]
pub struct BundleFileSystem {
    files: BTreeMap<String, Vec<u8>>,
    source_path: PathBuf,
    source_sha256: String,
}

/// Failure while loading an untrusted bundle.
#[derive(Debug, thiserror::Error)]
pub enum BundleLoadError {
    /// Filesystem failure.
    #[error("failed to read bundle path {path}: {source}")]
    Io {
        /// Path that failed.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// The bundle path is neither a directory nor a file.
    #[error("bundle path {0} is neither a directory nor a file")]
    UnsupportedPath(PathBuf),
    /// The bundle exceeded the policy byte budget.
    #[error("bundle exceeded max byte limit of {max_bytes} bytes")]
    BundleTooLarge {
        /// Policy limit that was exceeded.
        max_bytes: u64,
    },
    /// The archive could not be decoded.
    #[error("bundle archive is malformed: {0}")]
    MalformedArchive(String),
    /// No `manifest.json` at the bundle root or sole top-level directory.
    #[error("bundle has no manifest.json at its root or sole top-level directory")]
    MissingManifest,
    /// An entry path escaped the bundle root or was otherwise unsafe.
    #[error("bundle entry path `{0}` is not a safe relative path")]
    UnsafePath(String),
}

impl BundleFileSystem {
    /// Load a bundle directory or `.tar`/`.tar.zst` archive, bounded by `max_bytes`.
    pub fn load(path: impl AsRef<Path>, max_bytes: u64) -> Result<Self, BundleLoadError> {
        let path = path.as_ref();
        if path.is_dir() {
            Self::from_dir(path, max_bytes)
        } else if path.is_file() {
            Self::from_archive(path, max_bytes)
        } else {
            Err(BundleLoadError::UnsupportedPath(path.to_owned()))
        }
    }

    /// Every decoded file, keyed by safe bundle-relative path.
    #[must_use]
    pub fn files(&self) -> &BTreeMap<String, Vec<u8>> {
        &self.files
    }

    /// The on-disk path the bundle was loaded from.
    #[must_use]
    pub fn source_path(&self) -> &Path {
        &self.source_path
    }

    /// Deterministic SHA-256 identifying the bundle contents.
    #[must_use]
    pub fn source_sha256(&self) -> &str {
        &self.source_sha256
    }

    /// Read one bundle file.
    #[must_use]
    pub fn read(&self, path: &str) -> Option<&[u8]> {
        self.files.get(path).map(Vec::as_slice)
    }

    /// Read one bundle file as UTF-8 text.
    #[must_use]
    pub fn read_text(&self, path: &str) -> Option<Result<&str, std::str::Utf8Error>> {
        self.read(path).map(std::str::from_utf8)
    }

    /// Whether the bundle contains a file at `path`.
    #[must_use]
    pub fn contains_file(&self, path: &str) -> bool {
        self.files.contains_key(path)
    }

    /// Whether the bundle contains any file under `prefix`.
    #[must_use]
    pub fn has_prefix(&self, prefix: &str) -> bool {
        let prefix = normalize_prefix(prefix);
        self.files.keys().any(|path| path.starts_with(&prefix))
    }

    /// Every file under `prefix`, in deterministic path order.
    #[must_use]
    pub fn files_under(&self, prefix: &str) -> Vec<(&str, &[u8])> {
        let prefix = normalize_prefix(prefix);
        self.files
            .iter()
            .filter_map(|(path, bytes)| {
                path.strip_prefix(&prefix)
                    .map(|_| (path.as_str(), bytes.as_slice()))
            })
            .collect()
    }

    /// Deterministic `blake3:`-prefixed digest over every file under `prefix`.
    ///
    /// Returns `None` when the prefix is empty, so callers can distinguish
    /// "no such tree" from "empty tree digest".
    #[must_use]
    pub fn blake3_digest_for_prefix(&self, prefix: &str) -> Option<String> {
        let files = self.files_under(prefix);
        if files.is_empty() {
            return None;
        }
        let mut hasher = blake3::Hasher::new();
        for (path, bytes) in files {
            hasher.update(path.as_bytes());
            hasher.update(&[0]);
            hasher.update(bytes);
            hasher.update(&[0]);
        }
        Some(format!("blake3:{}", hasher.finalize().to_hex()))
    }

    fn from_dir(path: &Path, max_bytes: u64) -> Result<Self, BundleLoadError> {
        let root = discover_dir_root(path)?;
        let mut files = BTreeMap::new();
        let mut total_bytes = 0u64;
        read_dir_recursive(&root, &root, max_bytes, &mut total_bytes, &mut files)?;
        let source_sha256 = deterministic_tree_sha256(&files);
        Ok(Self {
            files,
            source_path: path.to_owned(),
            source_sha256,
        })
    }

    fn from_archive(path: &Path, max_bytes: u64) -> Result<Self, BundleLoadError> {
        let compressed_or_tar = read_file_limited(path, max_bytes)?;
        let source_sha256 = sha256_hex(&compressed_or_tar);
        let archive_bytes = if path
            .extension()
            .and_then(|ext| ext.to_str())
            .is_some_and(|ext| ext.eq_ignore_ascii_case("zst"))
        {
            let cursor = std::io::Cursor::new(compressed_or_tar.as_slice());
            let mut decoder = zstd::stream::read::Decoder::new(cursor)
                .map_err(|err| BundleLoadError::MalformedArchive(err.to_string()))?;
            read_to_end_limited(&mut decoder, max_bytes)?
        } else {
            compressed_or_tar
        };

        let files = strip_archive_root(parse_ustar(&archive_bytes)?)?;
        Ok(Self {
            files,
            source_path: path.to_owned(),
            source_sha256,
        })
    }
}

fn discover_dir_root(path: &Path) -> Result<PathBuf, BundleLoadError> {
    if path.join("manifest.json").is_file() {
        return Ok(path.to_owned());
    }

    let mut candidates = Vec::new();
    for entry in fs::read_dir(path).map_err(|source| BundleLoadError::Io {
        path: path.to_owned(),
        source,
    })? {
        let entry = entry.map_err(|source| BundleLoadError::Io {
            path: path.to_owned(),
            source,
        })?;
        let candidate = entry.path();
        if candidate.is_dir() && candidate.join("manifest.json").is_file() {
            candidates.push(candidate);
        }
    }
    if candidates.len() == 1 {
        Ok(candidates.remove(0))
    } else {
        Err(BundleLoadError::MissingManifest)
    }
}

fn read_dir_recursive(
    root: &Path,
    current: &Path,
    max_bytes: u64,
    total_bytes: &mut u64,
    files: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), BundleLoadError> {
    for entry in fs::read_dir(current).map_err(|source| BundleLoadError::Io {
        path: current.to_owned(),
        source,
    })? {
        let entry = entry.map_err(|source| BundleLoadError::Io {
            path: current.to_owned(),
            source,
        })?;
        let path = entry.path();
        if path.is_dir() {
            read_dir_recursive(root, &path, max_bytes, total_bytes, files)?;
            continue;
        }
        if !path.is_file() {
            continue;
        }
        let rel = relative_path(root, &path)?;
        let bytes = fs::read(&path).map_err(|source| BundleLoadError::Io {
            path: path.clone(),
            source,
        })?;
        *total_bytes = total_bytes.saturating_add(bytes.len() as u64);
        if *total_bytes > max_bytes {
            return Err(BundleLoadError::BundleTooLarge { max_bytes });
        }
        files.insert(rel, bytes);
    }
    Ok(())
}

fn relative_path(root: &Path, path: &Path) -> Result<String, BundleLoadError> {
    let rel = path
        .strip_prefix(root)
        .map_err(|_| BundleLoadError::UnsafePath(path.display().to_string()))?;
    let mut parts = Vec::new();
    for component in rel.components() {
        match component {
            Component::Normal(part) => parts.push(part.to_string_lossy().into_owned()),
            _ => return Err(BundleLoadError::UnsafePath(rel.display().to_string())),
        }
    }
    let rel = parts.join("/");
    if is_safe_relative_path(&rel) {
        Ok(rel)
    } else {
        Err(BundleLoadError::UnsafePath(rel))
    }
}

fn read_file_limited(path: &Path, max_bytes: u64) -> Result<Vec<u8>, BundleLoadError> {
    let mut file = fs::File::open(path).map_err(|source| BundleLoadError::Io {
        path: path.to_owned(),
        source,
    })?;
    read_to_end_limited(&mut file, max_bytes)
}

fn read_to_end_limited(reader: &mut impl Read, max_bytes: u64) -> Result<Vec<u8>, BundleLoadError> {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        let read = reader
            .read(&mut chunk)
            .map_err(|err| BundleLoadError::MalformedArchive(err.to_string()))?;
        if read == 0 {
            break;
        }
        buf.extend_from_slice(&chunk[..read]);
        if buf.len() as u64 > max_bytes {
            return Err(BundleLoadError::BundleTooLarge { max_bytes });
        }
    }
    Ok(buf)
}

fn parse_ustar(bytes: &[u8]) -> Result<BTreeMap<String, Vec<u8>>, BundleLoadError> {
    let mut files = BTreeMap::new();
    let mut offset = 0usize;
    while offset + 512 <= bytes.len() {
        let header = &bytes[offset..offset + 512];
        if header.iter().all(|byte| *byte == 0) {
            break;
        }

        let name = tar_string(&header[0..100]);
        let prefix = tar_string(&header[345..500]);
        let path = if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        };
        let typeflag = header[156];
        let normalized_path = path.trim_end_matches('/');
        if !is_safe_relative_path(normalized_path) {
            return Err(BundleLoadError::UnsafePath(path));
        }

        let size = parse_tar_octal(&header[124..136])?;
        offset += 512;
        let end = offset
            .checked_add(size)
            .ok_or_else(|| BundleLoadError::MalformedArchive("tar entry size overflow".into()))?;
        if end > bytes.len() {
            return Err(BundleLoadError::MalformedArchive(format!(
                "tar entry `{path}` exceeds archive length"
            )));
        }
        if typeflag == b'0' || typeflag == 0 {
            files.insert(normalized_path.to_owned(), bytes[offset..end].to_vec());
        }
        offset = align_512(end);
    }
    if !files.contains_key("manifest.json") {
        strip_archive_root(files.clone())?;
    }
    Ok(files)
}

fn strip_archive_root(
    files: BTreeMap<String, Vec<u8>>,
) -> Result<BTreeMap<String, Vec<u8>>, BundleLoadError> {
    if files.contains_key("manifest.json") {
        return Ok(files);
    }

    let mut roots = files
        .keys()
        .filter_map(|path| path.split_once('/'))
        .filter_map(|(root, rest)| (rest == "manifest.json").then_some(root.to_owned()))
        .collect::<Vec<_>>();
    roots.sort();
    roots.dedup();

    if roots.len() != 1 {
        return Err(BundleLoadError::MissingManifest);
    }
    let root = roots.remove(0);
    let prefix = format!("{root}/");
    let mut stripped = BTreeMap::new();
    for (path, bytes) in files {
        if let Some(rel) = path.strip_prefix(&prefix) {
            if !rel.is_empty() {
                stripped.insert(rel.to_owned(), bytes);
            }
        }
    }
    Ok(stripped)
}

fn parse_tar_octal(bytes: &[u8]) -> Result<usize, BundleLoadError> {
    let text = tar_string(bytes);
    usize::from_str_radix(text.trim(), 8)
        .map_err(|err| BundleLoadError::MalformedArchive(format!("invalid tar size: {err}")))
}

fn tar_string(bytes: &[u8]) -> String {
    let end = bytes
        .iter()
        .position(|byte| *byte == 0)
        .unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[..end]).trim().to_owned()
}

const fn align_512(value: usize) -> usize {
    (value + 511) & !511
}

fn normalize_prefix(prefix: &str) -> String {
    let trimmed = prefix.trim_matches('/');
    if trimmed.is_empty() {
        String::new()
    } else {
        format!("{trimmed}/")
    }
}

/// Lowercase hex SHA-256 of `bytes`.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hex_lower(&hasher.finalize())
}

fn deterministic_tree_sha256(files: &BTreeMap<String, Vec<u8>>) -> String {
    let mut hasher = Sha256::new();
    for (path, bytes) in files {
        hasher.update(path.as_bytes());
        hasher.update([0]);
        hasher.update(bytes);
        hasher.update([0]);
    }
    hex_lower(&hasher.finalize())
}

/// Encode `bytes` as lowercase hex.
#[must_use]
pub fn hex_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

/// Why a hex string could not be decoded.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HexDecodeError {
    /// Hex strings must have an even number of digits.
    #[error("hex string has odd length {0}")]
    OddLength(usize),
    /// A non-hex byte was present.
    #[error("hex string contains non-hex character `{0}`")]
    InvalidDigit(char),
}

/// Decode a lowercase- or uppercase-hex string into bytes.
///
/// Strict on purpose: registry public keys are hex-only, so any other encoding
/// must fail rather than be silently reinterpreted.
pub fn hex_decode(text: &str) -> Result<Vec<u8>, HexDecodeError> {
    let bytes = text.as_bytes();
    if !bytes.len().is_multiple_of(2) {
        return Err(HexDecodeError::OddLength(bytes.len()));
    }
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        let hi = hex_digit(pair[0])?;
        let lo = hex_digit(pair[1])?;
        out.push((hi << 4) | lo);
    }
    Ok(out)
}

fn hex_digit(byte: u8) -> Result<u8, HexDecodeError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => Err(HexDecodeError::InvalidDigit(char::from(byte))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hex_round_trip_lowercase() {
        let bytes = [0x00u8, 0x0f, 0xa5, 0xff];
        assert_eq!(hex_lower(&bytes), "000fa5ff");
        assert_eq!(hex_decode("000fa5ff").expect("valid hex decodes"), bytes);
        assert_eq!(hex_decode("000FA5FF").expect("valid hex decodes"), bytes);
    }

    #[test]
    fn test_hex_decode_rejects_malformed_input() {
        assert_eq!(hex_decode("abc"), Err(HexDecodeError::OddLength(3)));
        assert_eq!(hex_decode("zz"), Err(HexDecodeError::InvalidDigit('z')));
    }
}
