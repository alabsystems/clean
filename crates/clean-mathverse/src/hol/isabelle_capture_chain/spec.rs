// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The typed capture-chain spec (JSON): the source of truth the driver plans
//! and executes from. ROOT files are GENERATED from this spec; the spec is
//! never regenerated from ROOTs.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::error::CaptureChainError;

/// One chained capture segment: a single Isabelle session that re-elaborates
/// `theories` on `parent`'s heap under `record_proofs` and heap-saves (`-b`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Segment {
    /// Session name (also names the emitted `<dir>/ROOT` stanza).
    pub session: String,
    /// The `-d` directory the generated `ROOT` file is written into.
    pub dir: PathBuf,
    /// Fully-qualified theory references (`HOL-Library.Interval`) in
    /// downward-closed intra-chain build order.
    pub theories: Vec<String>,
    /// The parent heap this segment chains on (an earlier segment's session or
    /// an external base heap such as `ZP-Lib2`).
    pub parent: String,
    /// `record_proofs` recording level (4 = zproof capture; 2 = proofless
    /// heap-bake, the terminal ladder rung). Defaults to 4.
    #[serde(default = "default_record_proofs")]
    pub record_proofs: u32,
    /// Optional human note carried into the generated ROOT description (e.g.
    /// "Interval proofless bake").
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// Default `record_proofs` for a segment when the spec omits it.
#[must_use]
pub fn default_record_proofs() -> u32 {
    4
}

/// Where captured `.jsonl` proof files are moved after each OK build.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectSpec {
    /// The directory the capture hook writes into (heap-baked, at `at_end`).
    pub from_dir: PathBuf,
    /// The durable directory captures are relocated to.
    pub to_dir: PathBuf,
    /// Glob matched against file names in `from_dir` (`*`/`?` wildcards),
    /// e.g. `HOL-Library.*.jsonl`.
    pub glob: String,
}

/// Default global thread count (the Lib3 lesson: serialize `record_proofs`
/// elaboration so cumulative RSS never blows the arm64_32 store).
#[must_use]
pub fn default_threads() -> usize {
    1
}

/// A whole capture chain: an ordered list of segments plus the global build
/// options the driver shells `isabelle build` out with.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainSpec {
    /// The chained segments, in build order.
    pub segments: Vec<Segment>,
    /// `$ISABELLE_HOME` (the app dir whose `bin/isabelle` is invoked).
    pub isabelle_home: PathBuf,
    /// Extra `-d` directories (base heaps, upstream sessions) passed to every
    /// build in addition to each segment's own `dir`.
    #[serde(default)]
    pub dirs: Vec<PathBuf>,
    /// Global `threads` for `record_proofs` elaboration (default 1).
    #[serde(default = "default_threads")]
    pub threads: usize,
    /// Capture relocation config.
    pub collect: CollectSpec,
    /// Optional free-form comment (the example spec uses it to note Interval's
    /// proofless bake). Ignored by the driver.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub comment: Option<String>,
}

impl ChainSpec {
    /// Parse a spec from JSON bytes read from `path` (path is used only for
    /// error messages).
    ///
    /// # Errors
    /// [`CaptureChainError::SpecParse`] if the JSON does not deserialize.
    pub fn from_json_bytes(bytes: &[u8], path: &Path) -> Result<Self, CaptureChainError> {
        serde_json::from_slice(bytes).map_err(|source| CaptureChainError::SpecParse {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Read + parse a spec from a file.
    ///
    /// # Errors
    /// [`CaptureChainError::SpecRead`] on IO failure;
    /// [`CaptureChainError::SpecParse`] on malformed JSON.
    pub fn load(path: &Path) -> Result<Self, CaptureChainError> {
        let bytes = std::fs::read(path).map_err(|source| CaptureChainError::SpecRead {
            path: path.to_path_buf(),
            source,
        })?;
        Self::from_json_bytes(&bytes, path)
    }

    /// A stable content hash (SHA-256 hex of the canonical serialization) used
    /// to detect a changed spec on `--resume`.
    #[must_use]
    pub fn content_hash(&self) -> String {
        // serde_json serialization of this struct is deterministic (field order
        // is the declaration order, maps are not involved), so the hash is
        // stable for a given logical spec.
        let canonical = serde_json::to_vec(self).unwrap_or_default();
        let digest = Sha256::digest(&canonical);
        digest.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    /// Validate the spec's structural invariants: non-empty, unique session
    /// names, non-empty theory lists, no self- or forward parent reference,
    /// and a sane thread count.
    ///
    /// # Errors
    /// [`CaptureChainError::SpecInvalid`] with a human-readable reason.
    pub fn validate(&self) -> Result<(), CaptureChainError> {
        if self.segments.is_empty() {
            return Err(invalid("spec has no segments"));
        }
        if self.threads == 0 {
            return Err(invalid("threads must be >= 1"));
        }
        if self.isabelle_home.as_os_str().is_empty() {
            return Err(invalid("isabelle_home must be set"));
        }
        if self.collect.from_dir.as_os_str().is_empty()
            || self.collect.to_dir.as_os_str().is_empty()
            || self.collect.glob.is_empty()
        {
            return Err(invalid("collect.from_dir / to_dir / glob must all be set"));
        }
        let mut seen: Vec<&str> = Vec::with_capacity(self.segments.len());
        for (idx, seg) in self.segments.iter().enumerate() {
            if seg.session.is_empty() {
                return Err(invalid(&format!("segment {idx} has an empty session name")));
            }
            if seg.dir.as_os_str().is_empty() {
                return Err(invalid(&format!(
                    "segment {} has an empty dir",
                    seg.session
                )));
            }
            if seg.theories.is_empty() {
                return Err(invalid(&format!("segment {} has no theories", seg.session)));
            }
            if seg.parent == seg.session {
                return Err(invalid(&format!(
                    "segment {} lists itself as its parent",
                    seg.session
                )));
            }
            if seen.contains(&seg.session.as_str()) {
                return Err(invalid(&format!("duplicate session name {}", seg.session)));
            }
            // A parent that names a chain segment must be an EARLIER one; a
            // forward (or same-index) reference cannot resolve to a built heap.
            let parent_is_later = self.segments[idx..].iter().any(|s| s.session == seg.parent);
            if parent_is_later {
                return Err(invalid(&format!(
                    "segment {} chains on {}, which is not an earlier segment \
                     (forward reference)",
                    seg.session, seg.parent
                )));
            }
            seen.push(&seg.session);
        }
        Ok(())
    }
}

/// Build a [`CaptureChainError::SpecInvalid`] from a reason string.
fn invalid(reason: &str) -> CaptureChainError {
    CaptureChainError::SpecInvalid {
        reason: reason.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn minimal_json() -> &'static str {
        r#"{
          "segments": [
            {"session": "ZP-A", "dir": "zp_a", "theories": ["HOL-Library.Foo"], "parent": "ZP-Base"},
            {"session": "ZP-B", "dir": "zp_b", "theories": ["HOL-Library.Bar", "HOL-Library.Baz"], "parent": "ZP-A", "record_proofs": 4}
          ],
          "isabelle_home": "/opt/Isabelle",
          "dirs": ["zp_base"],
          "collect": {"from_dir": "from", "to_dir": "to", "glob": "HOL-Library.*.jsonl"}
        }"#
    }

    #[test]
    fn test_parse_defaults_record_proofs_and_threads() {
        let spec = ChainSpec::from_json_bytes(minimal_json().as_bytes(), Path::new("<t>"))
            .expect("minimal spec parses");
        assert_eq!(spec.threads, 1, "threads defaults to 1");
        assert_eq!(
            spec.segments[0].record_proofs, 4,
            "record_proofs defaults to 4"
        );
        assert_eq!(spec.segments[1].record_proofs, 4);
        spec.validate().expect("minimal spec is valid");
    }

    #[test]
    fn test_validate_rejects_empty_segments() {
        let spec = ChainSpec {
            segments: vec![],
            isabelle_home: "/opt".into(),
            dirs: vec![],
            threads: 1,
            collect: CollectSpec {
                from_dir: "a".into(),
                to_dir: "b".into(),
                glob: "*".into(),
            },
            comment: None,
        };
        assert!(matches!(
            spec.validate(),
            Err(CaptureChainError::SpecInvalid { .. })
        ));
    }

    #[test]
    fn test_validate_rejects_duplicate_session() {
        // The second segment repeats the session name; its parent is the
        // external base (not itself) so it reaches the duplicate check.
        let json = r#"{
          "segments": [
            {"session": "ZP-A", "dir": "d1", "theories": ["T.a"], "parent": "Base"},
            {"session": "ZP-A", "dir": "d2", "theories": ["T.b"], "parent": "Base"}
          ],
          "isabelle_home": "/opt", "collect": {"from_dir": "f", "to_dir": "t", "glob": "*"}
        }"#;
        let spec = ChainSpec::from_json_bytes(json.as_bytes(), Path::new("<t>")).expect("parses");
        let err = spec.validate().expect_err("duplicate session rejected");
        assert!(format!("{err}").contains("duplicate session"));
    }

    #[test]
    fn test_validate_rejects_forward_parent_reference() {
        let json = r#"{
          "segments": [
            {"session": "ZP-A", "dir": "d1", "theories": ["T.a"], "parent": "ZP-B"},
            {"session": "ZP-B", "dir": "d2", "theories": ["T.b"], "parent": "Base"}
          ],
          "isabelle_home": "/opt", "collect": {"from_dir": "f", "to_dir": "t", "glob": "*"}
        }"#;
        let spec = ChainSpec::from_json_bytes(json.as_bytes(), Path::new("<t>")).expect("parses");
        let err = spec.validate().expect_err("forward reference rejected");
        assert!(format!("{err}").contains("forward reference"));
    }

    #[test]
    fn test_shipped_example_spec_parses_and_validates() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../scripts/isabelle/lib3_backfill_chain.spec.json");
        // `scripts/isabelle/` is WORKSTATION ORCHESTRATION, deliberately kept
        // out of the public source snapshot (`publish/manifest.txt` excludes the
        // whole directory; this spec hard-codes one operator's Isabelle install
        // and `~/isabelle-work` corpus layout, which is meaningless off that
        // machine). This case asserts a property of that unpublished operator
        // artifact, so in a public checkout its input genuinely does not exist.
        //
        // Skip — deliberately and only for the absent-input case — rather than
        // fail there. The parser and every validation rule stay fully covered by
        // the inline-JSON cases in this module, which ship and run everywhere;
        // what is skipped is exclusively the "our checked-in example is still
        // shaped the way the driver expects" regression, which is only
        // meaningful where that example exists. Any OTHER load error (present
        // but malformed) still fails loudly through `expect` below.
        if !path.exists() {
            return;
        }
        let spec = ChainSpec::load(&path).expect("shipped example spec loads");
        spec.validate().expect("shipped example spec is valid");
        // Interval is deliberately bundled into the ZP-Lib3c2 band so the driver
        // self-heals it (proofless bake), reproducing tonight's manual split.
        let c2 = spec
            .segments
            .iter()
            .find(|s| s.session == "ZP-Lib3c2")
            .expect("example has the ZP-Lib3c2 band");
        assert!(
            c2.theories.iter().any(|t| t == "HOL-Library.Interval"),
            "Interval is bundled in ZP-Lib3c2 for the self-heal demo"
        );
        assert_eq!(
            spec.segments.last().map(|s| s.session.as_str()),
            Some("ZP-Lib3e"),
            "the chain ends at the post-Library heap"
        );
        assert_eq!(spec.threads, 1, "serialized per the Lib3 lesson");
    }

    #[test]
    fn test_content_hash_changes_with_content_and_is_stable() {
        let spec = ChainSpec::from_json_bytes(minimal_json().as_bytes(), Path::new("<t>"))
            .expect("parses");
        let h1 = spec.content_hash();
        let h2 = spec.content_hash();
        assert_eq!(h1, h2, "hash is stable for identical spec");
        assert_eq!(h1.len(), 64, "SHA-256 hex is 64 chars");
        let mut mutated = spec.clone();
        mutated.threads = 6;
        assert_ne!(
            h1,
            mutated.content_hash(),
            "hash changes when the spec changes"
        );
    }
}
