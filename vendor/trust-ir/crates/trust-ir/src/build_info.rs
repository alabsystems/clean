// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The build identity of THIS compiled `trust-ir` (roadmap WS8.4).
//!
//! Many commits share one package version (`0.14.0` spans dozens), so a bare
//! version string cannot tell two builds apart, and a consumer's manifest
//! string can lie (a `[patch]` redirects the dependency without changing it).
//! [`BUILD_IDENTITY`] is therefore read from the COMPILED crate: its package
//! version, the source sha resolved by `build.rs` (packaging override, then an
//! own-checkout `git` fallback, then `unknown` — see `build_identity.rs` at the
//! crate root), the wire version range this build writes and reads, and the
//! module-identity digest domain.
//!
//! Tools print [`BuildIdentity::version`] as `<MAJOR.MINOR.0>+<source>`, the
//! publication dev-build format, where `<source>` is `g<12-hex>` (packaging
//! attested a clean tree), `g<12-hex>.dirty`, `g<12-hex>.local` (a local
//! checkout; the working tree is NOT attested) or `unknown`.

use crate::binary;
use crate::imports::MODULE_IDENTITY_DOMAIN;

/// How [`BuildIdentity::source_sha`] was established.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SourceAttestation {
    /// Set by packaging (`ALAB_BUILD_GIT_SHA`), which attested the working
    /// tree clean (`ALAB_BUILD_GIT_DIRTY=0`).
    PackagedClean,
    /// Set by packaging, which attested the working tree dirty.
    PackagedDirty,
    /// Read by `git` from the crate's own checkout. The working tree is NOT
    /// attested: uncommitted changes may be compiled in.
    Local,
    /// No source identity was available. Never a guessed sha.
    Unknown,
}

impl SourceAttestation {
    /// Stable spelling, shared with the build script.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            SourceAttestation::PackagedClean => "packaged-clean",
            SourceAttestation::PackagedDirty => "packaged-dirty",
            SourceAttestation::Local => "local",
            SourceAttestation::Unknown => "unknown",
        }
    }

    /// Parse the build script's spelling. Any other value is a compile-time
    /// error when evaluated for [`BUILD_IDENTITY`], never a default.
    const fn from_build_env(s: &str) -> Self {
        if const_str_eq(s, "packaged-clean") {
            SourceAttestation::PackagedClean
        } else if const_str_eq(s, "packaged-dirty") {
            SourceAttestation::PackagedDirty
        } else if const_str_eq(s, "local") {
            SourceAttestation::Local
        } else if const_str_eq(s, "unknown") {
            SourceAttestation::Unknown
        } else {
            panic!("TIR_BUILD_ATTESTATION carries an unrecognised attestation")
        }
    }
}

const fn const_str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// The identity of a compiled `trust-ir`. See the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BuildIdentity {
    /// Cargo package name (`trust-ir`).
    pub package: &'static str,
    /// Cargo package version (`MAJOR.MINOR.0`).
    pub pkg_version: &'static str,
    /// `<pkg_version>+<source>`: what a tool's `--version` prints.
    pub version: &'static str,
    /// The SemVer build-metadata label: `g<12-hex>`, `g<12-hex>.dirty`,
    /// `g<12-hex>.local` or `unknown`.
    pub source: &'static str,
    /// The full source sha the label abbreviates, or `unknown`.
    pub source_sha: &'static str,
    /// How the sha was established.
    pub attestation: SourceAttestation,
    /// Wire version this build writes at most, and reads at most
    /// (`binary::VERSION`).
    pub wire_version: u32,
    /// Oldest wire version this build reads.
    pub min_read_version: u32,
    /// Versions inside `min_read_version..=wire_version` that are refused on
    /// read (the ambiguous-lineage range), as an inclusive `(first, last)`.
    pub refused_read_versions: (u32, u32),
    /// The domain under which `Module::stable_digest` names a module
    /// ([`MODULE_IDENTITY_DOMAIN`]).
    pub digest_domain: &'static str,
}

impl BuildIdentity {
    /// Whether a reader of this build accepts a blob of wire `version`.
    #[must_use]
    pub const fn reads(&self, version: u32) -> bool {
        version >= self.min_read_version
            && version <= self.wire_version
            && !(version >= self.refused_read_versions.0 && version <= self.refused_read_versions.1)
    }

    /// Whether this build's package version is exactly `version`. A tool
    /// that prints [`BUILD_IDENTITY`] as its OWN identity const-asserts this
    /// against its `CARGO_PKG_VERSION`, so it cannot silently report a
    /// different release's identity.
    #[must_use]
    pub const fn has_pkg_version(&self, version: &str) -> bool {
        const_str_eq(self.pkg_version, version)
    }

    /// One-line human summary of the readable wire range, e.g.
    /// `v23..=v25, v29..=v43 (v26..=v28 refused: ambiguous lineage)`.
    #[must_use]
    pub fn read_range_summary(&self) -> String {
        let (lo, hi) = self.refused_read_versions;
        format!(
            "v{}..=v{}, v{}..=v{} (v{lo}..=v{hi} refused: ambiguous lineage)",
            self.min_read_version,
            lo - 1,
            hi + 1,
            self.wire_version
        )
    }
}

/// The identity of this compiled `trust-ir`. Read it from the compiled crate,
/// never from a consumer's manifest.
pub const BUILD_IDENTITY: BuildIdentity = BuildIdentity {
    package: env!("CARGO_PKG_NAME"),
    pkg_version: env!("CARGO_PKG_VERSION"),
    version: concat!(env!("CARGO_PKG_VERSION"), "+", env!("TIR_BUILD_SOURCE")),
    source: env!("TIR_BUILD_SOURCE"),
    source_sha: env!("TIR_BUILD_GIT_SHA"),
    attestation: SourceAttestation::from_build_env(env!("TIR_BUILD_ATTESTATION")),
    wire_version: binary::VERSION,
    min_read_version: binary::MIN_READ_VERSION,
    refused_read_versions: (
        *binary::AMBIGUOUS_LINEAGE_VERSIONS.start(),
        *binary::AMBIGUOUS_LINEAGE_VERSIONS.end(),
    ),
    digest_domain: MODULE_IDENTITY_DOMAIN,
};

// The refused range must lie strictly inside the readable range, or
// `read_range_summary` would describe a range the reader does not implement.
const _: () = assert!(
    BUILD_IDENTITY.min_read_version < BUILD_IDENTITY.refused_read_versions.0
        && BUILD_IDENTITY.refused_read_versions.0 <= BUILD_IDENTITY.refused_read_versions.1
        && BUILD_IDENTITY.refused_read_versions.1 < BUILD_IDENTITY.wire_version
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_identity_agrees_with_the_reader() {
        let id = BUILD_IDENTITY;
        assert_eq!(id.wire_version, binary::VERSION);
        assert_eq!(id.digest_domain, "trust_ir.module.v3");
        assert!(id.version.starts_with(id.pkg_version));
        assert_eq!(id.version, format!("{}+{}", id.pkg_version, id.source));
        for v in 0..=binary::VERSION + 2 {
            let expected = (binary::MIN_READ_VERSION..=binary::VERSION).contains(&v)
                && !binary::AMBIGUOUS_LINEAGE_VERSIONS.contains(&v);
            assert_eq!(id.reads(v), expected, "v{v}");
        }
        assert_eq!(
            id.read_range_summary(),
            format!(
                "v23..=v25, v29..=v{} (v26..=v28 refused: ambiguous lineage)",
                binary::VERSION
            )
        );
    }

    #[test]
    fn source_label_matches_attestation() {
        let id = BUILD_IDENTITY;
        match id.attestation {
            SourceAttestation::Unknown => {
                assert_eq!(id.source, "unknown");
                assert_eq!(id.source_sha, "unknown");
            }
            att => {
                let short = &id.source_sha[..12];
                let expected = match att {
                    SourceAttestation::PackagedClean => format!("g{short}"),
                    SourceAttestation::PackagedDirty => format!("g{short}.dirty"),
                    _ => format!("g{short}.local"),
                };
                assert_eq!(id.source, expected);
            }
        }
    }
}
