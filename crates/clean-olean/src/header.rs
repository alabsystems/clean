// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! .olean file header parsing
//!
//! Lean4 has shipped at least two header layouts:
//!
//! ## Version 1
//! The header is exactly 56 bytes:
//! - 5 bytes: "olean" magic
//! - 1 byte: version (= 1)
//! - 42 bytes: git hash (40 chars + 2 null padding)
//! - 8 bytes: base address (little-endian u64)
//!
//! ## Version 2 (Lean4 v4.26+, confirmed against v4.30.0-rc2 `src/library/module.cpp`)
//! The header is exactly 88 bytes:
//! - 5 bytes: "olean" magic
//! - 1 byte: version (= 2)
//! - 1 byte: flags (bit 0: persisted bignums use GMP vs Lean-native encoding;
//!   bits 1-7 reserved). Relevant to faithful payload decoding.
//! - 33 bytes: Lean version string, `\0`-padded on the right and **not
//!   necessarily null-terminated** (e.g. `"4.30.0-rc2"`)
//! - 40 bytes: git hash, `\0`-padded on the right
//! - 8 bytes: base address (little-endian u64)

use crate::error::{OleanError, OleanResult};

/// Magic bytes at the start of every .olean file
pub const MAGIC: &[u8; 5] = b"olean";

/// Legacy .olean header version (Lean4 ≤ v4.13 toolchains)
pub const VERSION: u8 = 1;

/// New .olean header version (Lean4 ≥ v4.26 toolchains)
pub const VERSION_V2: u8 = 2;

/// Size of the v1 header in bytes
pub const HEADER_SIZE: usize = 56;

/// Size of the v2 header in bytes
pub const HEADER_SIZE_V2: usize = 88;

/// Size of the git hash field (includes null padding)
const GIT_HASH_FIELD_SIZE: usize = 42;

/// Size of actual git hash (40 hex characters)
const GIT_HASH_LEN: usize = 40;

/// Offset of the 1-byte flags field in the v2 header.
const FLAGS_OFFSET_V2: usize = 6;

/// Offset of the Lean version string in the v2 header.
const LEAN_VERSION_OFFSET_V2: usize = 7;

/// Length of the Lean version string field in the v2 header (`\0`-padded).
const LEAN_VERSION_LEN_V2: usize = 33;

/// Offset of the git hash in the v2 header.
const GIT_HASH_OFFSET_V2: usize = 40;

/// Offset of the base address in the v2 header.
const BASE_ADDR_OFFSET_V2: usize = 80;

/// Flags bit 0: persisted bignums use GMP encoding (vs Lean-native).
const FLAG_GMP_BIGNUMS: u8 = 0b1;

/// Parsed .olean file header
#[derive(Debug, Clone)]
pub struct OleanHeader {
    /// Magic bytes (should be "olean")
    pub magic: [u8; 5],

    /// Format version
    pub version: u8,

    /// Header flags (v2 only; bit 0 = persisted bignums use GMP encoding).
    /// Always `0` for v1 headers, which carry no flags byte.
    pub flags: u8,

    /// Lean toolchain version string from the v2 header (e.g. `"4.30.0-rc2"`).
    /// `None` for v1 headers, which carry no version string.
    pub lean_version: Option<String>,

    /// Git commit hash of the Lean build (40 chars, null-padded to 42)
    pub git_hash: [u8; GIT_HASH_FIELD_SIZE],

    /// Base address for memory mapping
    /// The compacted region was serialized with pointers relative to this address
    pub base_addr: u64,
}

impl OleanHeader {
    /// Parse an .olean header from bytes
    ///
    /// # REQUIRES
    /// - `bytes.len() >= 6` (minimum: magic + version to determine layout)
    ///
    /// # ENSURES
    /// - On success, `magic == b"olean"` and `version in {1, 2}`
    /// - On success, `git_hash` contains 40 valid hex characters
    /// - On `FileTooSmall` error, bytes.len() < required size for version
    /// - On `InvalidMagic` error, first 5 bytes != "olean"
    /// - On `UnsupportedVersion` error, version byte not in {1, 2}
    /// - On `InvalidGitHash` error, non-hex character found in hash
    ///
    /// Returns error if:
    /// - File is too small
    /// - Magic bytes don't match
    /// - Version is unsupported
    pub fn parse(bytes: &[u8]) -> OleanResult<Self> {
        // Need at least magic + version to decide layout.
        if bytes.len() < MAGIC.len() + 1 {
            return Err(OleanError::FileTooSmall {
                expected: MAGIC.len() + 1,
                actual: bytes.len(),
            });
        }

        // Parse magic
        let mut magic = [0u8; 5];
        magic.copy_from_slice(&bytes[0..5]);

        if &magic != MAGIC {
            return Err(OleanError::InvalidMagic(magic));
        }

        // Parse version
        let version = bytes[5];
        let (git_hash_offset, git_hash_len, base_addr_offset, min_size) = match version {
            VERSION => (6, GIT_HASH_FIELD_SIZE, 48, HEADER_SIZE),
            VERSION_V2 => (
                GIT_HASH_OFFSET_V2,
                GIT_HASH_LEN,
                BASE_ADDR_OFFSET_V2,
                HEADER_SIZE_V2,
            ),
            _ => {
                // Future formats (e.g. a hypothetical VERSION 3) are rejected with
                // a clear, actionable error rather than silently misparsed against
                // the v2 layout.
                return Err(OleanError::UnsupportedVersion {
                    expected: VERSION_V2,
                    actual: version,
                });
            }
        };

        if bytes.len() < min_size {
            return Err(OleanError::FileTooSmall {
                expected: min_size,
                actual: bytes.len(),
            });
        }

        // Parse v2-only fields: a 1-byte flags field followed by a 33-byte Lean
        // version string (`\0`-padded right, not necessarily null-terminated).
        let (flags, lean_version) = if version == VERSION_V2 {
            let flags = bytes[FLAGS_OFFSET_V2];
            let raw = &bytes[LEAN_VERSION_OFFSET_V2..LEAN_VERSION_OFFSET_V2 + LEAN_VERSION_LEN_V2];
            let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
            let version_str = String::from_utf8_lossy(&raw[..end]).into_owned();
            (flags, Some(version_str))
        } else {
            (0u8, None)
        };

        // Parse git hash: v1 copies the full 42-byte padded field; v2 copies 40.
        let mut git_hash = [0u8; GIT_HASH_FIELD_SIZE];
        git_hash[..git_hash_len]
            .copy_from_slice(&bytes[git_hash_offset..git_hash_offset + git_hash_len]);

        // Validate git hash (should be hex characters)
        for &b in &git_hash[..GIT_HASH_LEN] {
            if !b.is_ascii_hexdigit() {
                return Err(OleanError::InvalidGitHash(format!(
                    "non-hex character 0x{b:02x} in git hash"
                )));
            }
        }

        // Parse base address (little-endian)
        let base_addr = u64::from_le_bytes(
            bytes[base_addr_offset..base_addr_offset + 8]
                .try_into()
                .expect("header size verified above"),
        );

        Ok(Self {
            magic,
            version,
            flags,
            lean_version,
            git_hash,
            base_addr,
        })
    }

    /// Get the parsed Lean toolchain version string, if present (v2 headers).
    #[must_use]
    pub fn lean_version_str(&self) -> Option<&str> {
        self.lean_version.as_deref()
    }

    /// Whether persisted bignums in this module use GMP encoding (v2 flags bit 0).
    ///
    /// v1 headers have no flags byte; they are treated as not GMP-encoded.
    #[must_use]
    pub fn uses_gmp_bignums(&self) -> bool {
        self.flags & FLAG_GMP_BIGNUMS != 0
    }

    /// Get the git hash as a string (40 characters)
    ///
    /// # ENSURES
    /// - Returns a 40-character string (or `"<invalid utf8>"` on corruption)
    /// - All characters are lowercase hex digits (0-9, a-f) for valid headers
    pub fn git_hash_str(&self) -> &str {
        // The first 40 bytes are the hash, rest is null padding
        std::str::from_utf8(&self.git_hash[..GIT_HASH_LEN]).unwrap_or("<invalid utf8>")
    }

    /// Get the short git hash (first 12 characters, like Lean displays)
    ///
    /// # ENSURES
    /// - Returns exactly 12 characters (prefix of `git_hash_str()`)
    pub fn git_hash_short(&self) -> &str {
        &self.git_hash_str()[..12]
    }

    /// Check if this header is compatible with a given git hash
    ///
    /// # ENSURES
    /// - Returns true if `git_hash_str()` starts with `hash` (up to 40 chars)
    /// - Empty `hash` always returns true (vacuous match)
    ///
    /// Returns true if the first `len` characters match
    pub fn matches_git_hash(&self, hash: &str) -> bool {
        let our_hash = self.git_hash_str();
        let len = hash.len().min(GIT_HASH_LEN);
        our_hash[..len] == hash[..len]
    }

    /// Create a new header with the given git hash and base address
    ///
    /// # REQUIRES
    /// - `git_hash.len() == 40`
    /// - All characters in `git_hash` are hex digits (0-9, a-f, A-F)
    ///
    /// # ENSURES
    /// - On success, `magic == b"olean"` and `version == 1`
    /// - On success, `git_hash_str() == git_hash`
    /// - On success, `base_addr` equals the provided value
    pub fn new(git_hash: &str, base_addr: u64) -> OleanResult<Self> {
        if git_hash.len() != GIT_HASH_LEN {
            return Err(OleanError::InvalidGitHash(format!(
                "expected {} characters, got {}",
                GIT_HASH_LEN,
                git_hash.len()
            )));
        }

        for c in git_hash.chars() {
            if !c.is_ascii_hexdigit() {
                return Err(OleanError::InvalidGitHash(format!(
                    "non-hex character '{c}' in git hash"
                )));
            }
        }

        let mut git_hash_bytes = [0u8; GIT_HASH_FIELD_SIZE];
        git_hash_bytes[..GIT_HASH_LEN].copy_from_slice(git_hash.as_bytes());

        Ok(Self {
            magic: *MAGIC,
            version: VERSION,
            flags: 0,
            lean_version: None,
            git_hash: git_hash_bytes,
            base_addr,
        })
    }

    /// Serialize the header to bytes
    ///
    /// # ENSURES
    /// - Returns exactly `HEADER_SIZE` (56) bytes
    /// - `OleanHeader::parse(&serialize())` equals `self` (roundtrip)
    pub fn serialize(&self) -> [u8; HEADER_SIZE] {
        let mut bytes = [0u8; HEADER_SIZE];

        // Magic
        bytes[0..5].copy_from_slice(&self.magic);

        // Version
        bytes[5] = self.version;

        // Git hash
        bytes[6..48].copy_from_slice(&self.git_hash);

        // Base address (little-endian)
        bytes[48..56].copy_from_slice(&self.base_addr.to_le_bytes());

        bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_header_size() {
        // Verify our size constant matches the struct layout
        assert_eq!(HEADER_SIZE, 56);
        assert_eq!(GIT_HASH_FIELD_SIZE, 42);
    }

    #[test]
    fn test_parse_valid_header() {
        // Construct a valid header
        let mut bytes = vec![0u8; HEADER_SIZE];

        // Magic
        bytes[0..5].copy_from_slice(b"olean");

        // Version
        bytes[5] = 1;

        // Git hash (40 hex chars + 2 null)
        bytes[6..46].copy_from_slice(b"0123456789abcdef0123456789abcdef01234567");
        bytes[46] = 0;
        bytes[47] = 0;

        // Base address (0x1234567890abcdef little-endian)
        bytes[48..56].copy_from_slice(&0x1234_5678_90ab_cdef_u64.to_le_bytes());

        let header = OleanHeader::parse(&bytes).expect("Should parse valid header");

        assert_eq!(header.magic, *b"olean");
        assert_eq!(header.version, 1);
        assert_eq!(
            header.git_hash_str(),
            "0123456789abcdef0123456789abcdef01234567"
        );
        assert_eq!(header.git_hash_short(), "0123456789ab");
        assert_eq!(header.base_addr, 0x1234_5678_90ab_cdef);

        assert!(header.matches_git_hash("0123456789ab"));
        assert!(header.matches_git_hash("0123456789abcdef0123456789abcdef01234567"));
        assert!(!header.matches_git_hash("aaaaaaaaaa"));
    }

    #[test]
    fn test_parse_too_small() {
        // Not enough bytes to read magic + version
        let bytes = vec![0u8; MAGIC.len()];
        let err = OleanHeader::parse(&bytes).unwrap_err();
        assert!(matches!(err, OleanError::FileTooSmall { .. }));
    }

    #[test]
    fn test_parse_invalid_magic() {
        let mut bytes = vec![0u8; HEADER_SIZE];
        bytes[0..5].copy_from_slice(b"notok");

        let err = OleanHeader::parse(&bytes).unwrap_err();
        assert!(matches!(err, OleanError::InvalidMagic(_)));
    }

    #[test]
    fn test_parse_invalid_version() {
        let mut bytes = vec![0u8; HEADER_SIZE];
        bytes[0..5].copy_from_slice(b"olean");
        bytes[5] = 99; // Invalid version

        let err = OleanHeader::parse(&bytes).unwrap_err();
        assert!(matches!(err, OleanError::UnsupportedVersion { .. }));
    }

    #[test]
    fn test_parse_invalid_git_hash() {
        let mut bytes = vec![0u8; HEADER_SIZE];
        bytes[0..5].copy_from_slice(b"olean");
        bytes[5] = 1;
        bytes[6..46].copy_from_slice(b"not_a_valid_hex_hash!!!!!!!!!!!!!!!!!!!!"); // Invalid

        let err = OleanHeader::parse(&bytes).unwrap_err();
        assert!(matches!(err, OleanError::InvalidGitHash(_)));
    }

    fn make_header_with_hash(hash: &str) -> OleanHeader {
        let mut bytes = vec![0u8; HEADER_SIZE];
        bytes[0..5].copy_from_slice(b"olean");
        bytes[5] = 1;
        bytes[6..46].copy_from_slice(hash.as_bytes());
        bytes[46] = 0;
        bytes[47] = 0;
        bytes[48..56].copy_from_slice(&0u64.to_le_bytes());
        OleanHeader::parse(&bytes).unwrap()
    }

    #[test]
    fn test_git_hash_short_returns_12_chars() {
        let header = make_header_with_hash("abcdef1234567890abcdef1234567890abcdef12");
        let short = header.git_hash_short();
        assert_eq!(short.len(), 12);
        assert_eq!(short, "abcdef123456");
    }

    #[test]
    fn test_git_hash_str_returns_40_chars() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let header = make_header_with_hash(hash);
        assert_eq!(header.git_hash_str().len(), 40);
        assert_eq!(header.git_hash_str(), hash);
    }

    #[test]
    fn test_matches_git_hash_empty_string() {
        let header = make_header_with_hash("0123456789abcdef0123456789abcdef01234567");
        // Empty string should match anything (vacuous truth)
        assert!(header.matches_git_hash(""));
    }

    #[test]
    fn test_matches_git_hash_partial_prefix() {
        let header = make_header_with_hash("0123456789abcdef0123456789abcdef01234567");
        assert!(header.matches_git_hash("0"));
        assert!(header.matches_git_hash("01"));
        assert!(header.matches_git_hash("0123"));
        assert!(header.matches_git_hash("0123456789ab"));
        assert!(!header.matches_git_hash("1"));
        assert!(!header.matches_git_hash("abcdef"));
    }

    #[test]
    fn test_matches_git_hash_full_match() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let header = make_header_with_hash(hash);
        assert!(header.matches_git_hash(hash));
    }

    #[test]
    fn test_matches_git_hash_longer_than_stored() {
        let header = make_header_with_hash("0123456789abcdef0123456789abcdef01234567");
        // If input is longer than 40 chars, only compare first 40
        let long_hash = "0123456789abcdef0123456789abcdef01234567extra";
        assert!(header.matches_git_hash(long_hash));
    }

    #[test]
    fn test_matches_git_hash_case_sensitive() {
        let header = make_header_with_hash("abcdef1234567890abcdef1234567890abcdef12");
        // Hash matching is case sensitive
        assert!(header.matches_git_hash("abcdef"));
        assert!(!header.matches_git_hash("ABCDEF"));
    }

    #[test]
    fn test_git_hash_all_zeros() {
        let header = make_header_with_hash("0000000000000000000000000000000000000000");
        assert_eq!(
            header.git_hash_str(),
            "0000000000000000000000000000000000000000"
        );
        assert_eq!(header.git_hash_short(), "000000000000");
        assert!(header.matches_git_hash("0000"));
    }

    #[test]
    fn test_git_hash_all_fs() {
        let header = make_header_with_hash("ffffffffffffffffffffffffffffffffffffffff");
        assert_eq!(
            header.git_hash_str(),
            "ffffffffffffffffffffffffffffffffffffffff"
        );
        assert_eq!(header.git_hash_short(), "ffffffffffff");
        assert!(header.matches_git_hash("ffff"));
    }

    #[test]
    fn test_header_new() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let header = OleanHeader::new(hash, 0x1000).unwrap();

        assert_eq!(header.magic, *b"olean");
        assert_eq!(header.version, 1);
        assert_eq!(header.git_hash_str(), hash);
        assert_eq!(header.base_addr, 0x1000);
    }

    #[test]
    fn test_header_new_invalid_length() {
        let err = OleanHeader::new("tooshort", 0x1000).unwrap_err();
        assert!(matches!(err, OleanError::InvalidGitHash(_)));
    }

    #[test]
    fn test_header_new_invalid_char() {
        let err = OleanHeader::new("0123456789abcdef0123456789abcdef0123456g", 0x1000).unwrap_err();
        assert!(matches!(err, OleanError::InvalidGitHash(_)));
    }

    #[test]
    fn test_header_serialize_roundtrip() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let original = OleanHeader::new(hash, 0x1234_5678_90ab_cdef).unwrap();
        let bytes = original.serialize();

        assert_eq!(bytes.len(), HEADER_SIZE);

        let parsed = OleanHeader::parse(&bytes).unwrap();
        assert_eq!(parsed.magic, original.magic);
        assert_eq!(parsed.version, original.version);
        assert_eq!(parsed.git_hash, original.git_hash);
        assert_eq!(parsed.base_addr, original.base_addr);
    }

    #[test]
    fn test_header_serialize_format() {
        let hash = "abcdef1234567890abcdef1234567890abcdef12";
        let header = OleanHeader::new(hash, 0x0100).unwrap();
        let bytes = header.serialize();

        // Check magic
        assert_eq!(&bytes[0..5], b"olean");
        // Check version
        assert_eq!(bytes[5], 1);
        // Check git hash
        assert_eq!(&bytes[6..46], hash.as_bytes());
        // Check null padding
        assert_eq!(bytes[46], 0);
        assert_eq!(bytes[47], 0);
        // Check base address (0x0100 in little-endian)
        assert_eq!(
            &bytes[48..56],
            &[0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
    }

    /// Build a synthetic v2 header matching the v4.30 on-disk layout:
    /// magic(5) + version(1) + flags(1) + lean_version(33) + githash(40) + base_addr(8).
    fn make_v2_header(flags: u8, lean_version: &str, git_hash: &str, base_addr: u64) -> Vec<u8> {
        let mut bytes = vec![0u8; HEADER_SIZE_V2];
        bytes[0..5].copy_from_slice(b"olean");
        bytes[5] = VERSION_V2;
        bytes[FLAGS_OFFSET_V2] = flags;
        let vbytes = lean_version.as_bytes();
        let n = vbytes.len().min(LEAN_VERSION_LEN_V2);
        bytes[LEAN_VERSION_OFFSET_V2..LEAN_VERSION_OFFSET_V2 + n].copy_from_slice(&vbytes[..n]);
        bytes[GIT_HASH_OFFSET_V2..GIT_HASH_OFFSET_V2 + GIT_HASH_LEN]
            .copy_from_slice(git_hash.as_bytes());
        bytes[BASE_ADDR_OFFSET_V2..BASE_ADDR_OFFSET_V2 + 8]
            .copy_from_slice(&base_addr.to_le_bytes());
        bytes
    }

    #[test]
    fn test_parse_v2_header_extracts_version_flags_hash() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let bytes = make_v2_header(FLAG_GMP_BIGNUMS, "4.30.0-rc2", hash, 0x7f00_0000_0000);
        let header = OleanHeader::parse(&bytes).expect("v2 header must parse");

        assert_eq!(header.version, VERSION_V2);
        assert_eq!(header.lean_version_str(), Some("4.30.0-rc2"));
        assert!(header.uses_gmp_bignums(), "flags bit 0 set => GMP bignums");
        assert_eq!(header.git_hash_str(), hash);
        assert_eq!(header.base_addr, 0x7f00_0000_0000);
    }

    #[test]
    fn test_parse_v2_header_native_bignums_flag_clear() {
        let hash = "abcdef1234567890abcdef1234567890abcdef12";
        let bytes = make_v2_header(0, "4.30.0", hash, 0);
        let header = OleanHeader::parse(&bytes).expect("v2 header must parse");
        assert!(
            !header.uses_gmp_bignums(),
            "flags bit 0 clear => Lean-native bignums"
        );
        assert_eq!(header.lean_version_str(), Some("4.30.0"));
    }

    #[test]
    fn test_v1_header_has_no_lean_version_or_flags() {
        let header = make_header_with_hash("0123456789abcdef0123456789abcdef01234567");
        assert_eq!(header.version, VERSION);
        assert_eq!(header.lean_version_str(), None);
        assert!(!header.uses_gmp_bignums());
        assert_eq!(header.flags, 0);
    }

    #[test]
    fn test_parse_v2_version_string_null_padded_not_terminated() {
        // Fill the entire 33-byte field with a long version with no null terminator.
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let long_ver = "4.30.0-nightly-2026-06-23-extra33"; // exactly 33 chars
        assert_eq!(long_ver.len(), LEAN_VERSION_LEN_V2);
        let bytes = make_v2_header(0, long_ver, hash, 0);
        let header = OleanHeader::parse(&bytes).expect("v2 header must parse");
        assert_eq!(header.lean_version_str(), Some(long_ver));
    }
}
