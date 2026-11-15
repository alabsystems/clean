//! Content-addressed incremental cache for the PARAGON parallel verifier.
//!
//! This is paragon property #2 — *the "import again and again efficiently"
//! feature*. Each module's verdict is keyed on the blake3 hash of its transitive
//! `.olean` import closure, folded with the kernel/elision **fingerprint**.
//!
//! Why a closure hash is the *complete and correct* key: a module's verification
//! verdict is a pure function of the bytes of every part the loader reads for it
//! and for everything it transitively imports — each closure member's `.olean`,
//! `.olean.server` and `.olean.private`, trailers included (its terms cannot
//! reference any constant outside that closure — see
//! [`clean_olean::verify_batch::build_import_closures`]) — together with the
//! kernel behaviour the fingerprint pins down. Therefore:
//!
//! * fingerprint change (kernel/heartbeat/elision/…) ⇒ every closure hash
//!   changes ⇒ a full, honest re-verify;
//! * one changed part of a module ⇒ only that module **and its transitive
//!   dependents** (the modules whose closures contain it) get a new hash ⇒ only
//!   they re-run;
//! * nothing changed ⇒ every hash matches ⇒ a near-instant re-import.
//!
//! Before R113 (docs/DECISIONS.md) only the `.olean` of each member was hashed,
//! so a replaced `.olean.private` or `.olean.server` replayed a verdict minted
//! over parts the base no longer held (finding B2).
//!
//! The cache never makes a verdict *more* trusting: a hit replays a verdict the
//! kernel already minted for byte-identical inputs under an identical
//! fingerprint. A miss (or a missing/!-existent shard on disk) always falls back
//! to a fresh `check_decl_readonly`. Corrupt/old-schema cache files load as
//! empty (cold start), never as wrong answers.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::parallel_verify::ModuleVerdicts;

/// Cache schema version. Bump on any change to [`ModuleVerdicts`]'s shape or to
/// the closure-hash recipe — older files then load as empty (a safe cold start).
/// Version 2 (R113) hashes every part of each closure member, not its `.olean`
/// alone, so a version-1 cache keyed on `.olean` bytes is never served.
pub(crate) const CACHE_SCHEMA_VERSION: u32 = 2;

/// One module's cached verdict, tagged with the closure hash it was computed for.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CachedModule {
    /// blake3 hex of `fingerprint ‖ {path=filehash}` over the SORTED closure.
    pub(crate) closure_hash: String,
    /// The verdict to replay verbatim on a hit.
    pub(crate) verdicts: ModuleVerdicts,
}

/// On-disk incremental cache (one JSON sidecar next to the shard out-dir).
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct ImportCache {
    pub(crate) schema_version: u32,
    /// Human-readable fingerprint (diagnostic only — the authoritative key is
    /// each module's `closure_hash`, which already folds the fingerprint in).
    pub(crate) fingerprint: String,
    /// `olean path string` → cached verdict.
    pub(crate) modules: BTreeMap<String, CachedModule>,
}

impl ImportCache {
    /// A fresh, empty cache stamped with the current schema and a fingerprint.
    pub(crate) fn new(fingerprint: &str) -> Self {
        Self {
            schema_version: CACHE_SCHEMA_VERSION,
            fingerprint: fingerprint.to_string(),
            modules: BTreeMap::new(),
        }
    }

    /// Load a cache file. A missing, unreadable, malformed, or stale-schema file
    /// yields an empty cache (cold start) — never an error and never a wrong key.
    pub(crate) fn load(path: &Path) -> Self {
        let Ok(bytes) = std::fs::read(path) else {
            return Self::default();
        };
        match serde_json::from_slice::<ImportCache>(&bytes) {
            Ok(c) if c.schema_version == CACHE_SCHEMA_VERSION => c,
            _ => Self::default(),
        }
    }

    /// Persist the cache atomically-ish (write then rename) so an interrupted
    /// write never leaves a half-written, schema-valid-looking file.
    pub(crate) fn save(&self, path: &Path) -> std::io::Result<()> {
        let bytes = serde_json::to_vec_pretty(self)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        let tmp = path.with_extension("import_cache.tmp");
        std::fs::write(&tmp, &bytes)?;
        std::fs::rename(&tmp, path)
    }

    /// The cached entry for an olean, if any.
    pub(crate) fn get(&self, olean: &Path) -> Option<&CachedModule> {
        self.modules.get(&olean.display().to_string())
    }

    /// Record a module's verdict under its current closure hash.
    pub(crate) fn insert(&mut self, olean: &Path, closure_hash: String, verdicts: ModuleVerdicts) {
        self.modules.insert(
            olean.display().to_string(),
            CachedModule {
                closure_hash,
                verdicts,
            },
        );
    }
}

/// Compute the content-addressed closure hash for every target olean.
///
/// `fingerprint` must fold in everything that can change a verdict (kernel
/// version, heartbeat, elision policy, closure-modules cap, prelude variant).
/// Per-file blake3 hashes are memoized — a single base module appears in many
/// closures, so we read and hash each `.olean` at most once.
///
/// `search_paths` must be the SAME set the PARAGON base loads from
/// (`build_paragon_search_paths`: root + sibling Lake packages +
/// `default_search_paths`). The closure is resolved across all of them so an
/// out-of-`root` dependency change (a stdlib/Batteries/Aesop/lake-package bump)
/// re-keys every module whose closure contains it — closing the stale-reuse gap
/// that a root-only closure left open.
///
/// A member's digest is [`crate::cli::closure_load::source_olean_digest`]: its
/// `.olean`, `.olean.private` and `.olean.server`, each length-prefixed, an
/// absent companion a length-0 region — every part the base loader reads. A
/// member whose part exists but cannot be read leaves every target holding it
/// WITHOUT a hash, which is a cache miss (never the hash of an empty file).
pub(crate) fn compute_closure_hashes(
    oleans: &[PathBuf],
    root: &Path,
    search_paths: &[&Path],
    fingerprint: &str,
) -> HashMap<PathBuf, String> {
    let closures = clean_olean::verify_batch::build_import_closures_with_search_paths(
        oleans,
        root,
        search_paths,
    );

    // Digest the parts of every member appearing in any closure, once each;
    // `None` for a member some part of which could not be read.
    let mut file_hash: HashMap<PathBuf, Option<String>> = HashMap::new();
    for members in closures.values() {
        for p in members {
            if !file_hash.contains_key(p) {
                let h = crate::cli::closure_load::source_olean_digest(p)
                    .ok()
                    .map(|(digest, _len)| blake3::Hash::from(digest).to_hex().to_string());
                file_hash.insert(p.clone(), h);
            }
        }
    }

    // Per target: blake3 over (fingerprint, then each closure member's
    // `path=partsdigest`). build_import_closures already sorts members, so the
    // digest is deterministic and order-independent across runs. A member whose
    // parts could not be read drops its target: no key, so it misses the cache.
    let mut out: HashMap<PathBuf, String> = HashMap::new();
    'targets: for (target, members) in &closures {
        let mut hasher = blake3::Hasher::new();
        hasher.update(fingerprint.as_bytes());
        hasher.update(b"\x00");
        for p in members {
            let Some(Some(digest)) = file_hash.get(p) else {
                continue 'targets;
            };
            hasher.update(p.to_string_lossy().as_bytes());
            hasher.update(b"=");
            hasher.update(digest.as_bytes());
            hasher.update(b"\x00");
        }
        out.insert(target.clone(), hasher.finalize().to_hex().to_string());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_verdicts() -> ModuleVerdicts {
        // ModuleVerdicts is Default; that is enough to exercise serde round-trip.
        ModuleVerdicts::default()
    }

    #[test]
    fn test_cache_roundtrip_and_get() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join(".import_cache.json");
        let mut cache = ImportCache {
            schema_version: CACHE_SCHEMA_VERSION,
            fingerprint: "fp-1".to_string(),
            modules: BTreeMap::new(),
        };
        let olean = PathBuf::from("/x/Foo.olean");
        cache.insert(&olean, "hash-abc".to_string(), sample_verdicts());
        cache.save(&path).expect("save");

        let loaded = ImportCache::load(&path);
        assert_eq!(loaded.schema_version, CACHE_SCHEMA_VERSION);
        let hit = loaded.get(&olean).expect("entry present after roundtrip");
        assert_eq!(hit.closure_hash, "hash-abc");
    }

    #[test]
    fn test_load_missing_file_is_empty_not_error() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cache = ImportCache::load(&dir.path().join("does-not-exist.json"));
        assert_eq!(cache.schema_version, 0); // Default => cold start
        assert!(cache.modules.is_empty());
    }

    #[test]
    fn test_stale_schema_loads_as_cold_start() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("c.json");
        // A syntactically valid cache with a future/incompatible schema version.
        std::fs::write(
            &path,
            br#"{"schema_version":999999,"fingerprint":"x","modules":{}}"#,
        )
        .expect("write");
        let cache = ImportCache::load(&path);
        assert_eq!(
            cache.schema_version, 0,
            "incompatible schema must load as empty, never as a stale hit"
        );
    }

    #[test]
    fn test_corrupt_file_loads_as_cold_start() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("c.json");
        std::fs::write(&path, b"not json at all }{").expect("write");
        let cache = ImportCache::load(&path);
        assert!(cache.modules.is_empty());
    }

    /// The committed Char→Init stdlib fixtures, relative to this crate's manifest.
    fn stdlib_fixture() -> (PathBuf, PathBuf) {
        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.13.0/stdlib");
        (fixture.join("Init/Char.olean"), fixture.join("Init.olean"))
    }

    /// CORRECTNESS: an OUT-OF-ROOT dependency change must invalidate the cache
    /// key. The PARAGON base loads deps across all search paths, so a stdlib /
    /// Lake-package / toolchain bump that changes a dependency's bytes must
    /// re-key every dependent — otherwise a stale verdict is reused. We split the
    /// Char→Init fixture so Init lives OUTSIDE `root`, supply Init's dir as a
    /// search path, then mutate Init's bytes and assert Char's hash changes.
    #[test]
    fn test_out_of_root_dep_change_rekeys_closure_hash() {
        let (src_char, src_init) = stdlib_fixture();
        if !src_char.exists() || !src_init.exists() {
            return; // committed fixtures; skip if a checkout omits them
        }
        let tmp = tempfile::tempdir().expect("tempdir");
        let root = tmp.path().join("root");
        let deproot = tmp.path().join("deproot");
        std::fs::create_dir_all(root.join("Init")).expect("mkdir");
        std::fs::create_dir_all(&deproot).expect("mkdir");
        let char_m = root.join("Init/Char.olean");
        let init_m = deproot.join("Init.olean");
        std::fs::copy(&src_char, &char_m).expect("copy Char");
        std::fs::copy(&src_init, &init_m).expect("copy Init");

        let search: Vec<&Path> = vec![root.as_path(), deproot.as_path()];
        let h1 = compute_closure_hashes(std::slice::from_ref(&char_m), &root, &search, "fp")
            .remove(&char_m)
            .expect("Char hash");

        // Mutate the OUT-OF-ROOT dependency's bytes.
        let mut init_bytes = std::fs::read(&init_m).expect("read Init");
        init_bytes.push(0xAB);
        std::fs::write(&init_m, &init_bytes).expect("write Init");

        let h2 = compute_closure_hashes(std::slice::from_ref(&char_m), &root, &search, "fp")
            .remove(&char_m)
            .expect("Char hash");
        assert_ne!(
            h1, h2,
            "an out-of-root dep change MUST re-key the dependent's closure hash"
        );
    }

    /// `Char`'s closure copied into a fresh root, with `Init` beside it.
    fn char_closure(tmp: &Path) -> (PathBuf, PathBuf) {
        let (src_char, src_init) = stdlib_fixture();
        let root = tmp.join("root");
        std::fs::create_dir_all(root.join("Init")).expect("mkdir");
        let char_m = root.join("Init/Char.olean");
        std::fs::copy(&src_char, &char_m).expect("copy the committed Char fixture");
        std::fs::copy(&src_init, root.join("Init.olean")).expect("copy the committed Init fixture");
        (root, char_m)
    }

    fn char_hash(root: &Path, char_m: &Path) -> Option<String> {
        let search: Vec<&Path> = vec![root];
        compute_closure_hashes(&[char_m.to_path_buf()], root, &search, "fp").remove(char_m)
    }

    /// B2 (R113): the loader reads a closure member's `.olean.server` and
    /// `.olean.private` too (and any trailer each carries), so a change to
    /// either must leave no closure holding the member on its old key. Before
    /// R113 only `.olean` bytes were hashed, so `--incremental` replayed a
    /// stale verdict over parts it never read.
    ///
    /// The committed fixture has no companion parts, and the parts written
    /// here are ones the artifact reader refuses. On the target that leaves
    /// Char without a key (the closure walk cannot read it: a cache miss). On
    /// the dependency `Init` the walk keeps the member and the key hashes the
    /// part's bytes, so each content keys Char differently.
    #[test]
    fn test_companion_change_rekeys_closure_hash() {
        for companion in ["olean.private", "olean.server"] {
            for member in ["Init/Char.olean", "Init.olean"] {
                let tmp = tempfile::tempdir().expect("tempdir");
                let (root, char_m) = char_closure(tmp.path());
                let without = char_hash(&root, &char_m).expect("Char hashes without the part");
                let part = root.join(member).with_extension(companion);
                std::fs::write(&part, b"first part bytes").expect("write part");
                let first = char_hash(&root, &char_m);
                std::fs::write(&part, b"other part bytes").expect("rewrite part");
                let other = char_hash(&root, &char_m);
                match member {
                    "Init/Char.olean" => assert_eq!(
                        (first.as_deref(), other.as_deref()),
                        (None, None),
                        "a `.{companion}` the reader refuses must leave the target Char without a key"
                    ),
                    _ => {
                        let first = first.expect("Char keyed over a dependency's part");
                        let other = other.expect("Char keyed over a dependency's part");
                        assert_ne!(
                            first, without,
                            "an added `{member}` `.{companion}` must re-key Char's closure hash"
                        );
                        assert_ne!(
                            other, first,
                            "a changed `{member}` `.{companion}` must re-key Char's closure hash"
                        );
                    }
                }
                std::fs::remove_file(&part).expect("remove part");
                assert_eq!(
                    char_hash(&root, &char_m).as_deref(),
                    Some(without.as_str()),
                    "removing the `{member}` `.{companion}` must restore Char's key without it"
                );
            }
        }
    }

    /// The digest every closure key is built from covers each part's bytes, so a
    /// companion change re-keys whatever the closure walk makes of it.
    #[test]
    fn test_source_olean_digest_covers_every_part() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let (_root, char_m) = char_closure(tmp.path());
        let digest = || {
            crate::cli::closure_load::source_olean_digest(&char_m)
                .expect("digest Char's parts")
                .0
        };
        let without = digest();
        let mut seen = vec![without];
        for companion in ["olean.private", "olean.server"] {
            let part = char_m.with_extension(companion);
            for bytes in [&b"first part bytes"[..], &b"other part bytes"[..]] {
                std::fs::write(&part, bytes).expect("write part");
                let d = digest();
                assert!(
                    !seen.contains(&d),
                    "`.{companion}` content {bytes:?} must give a digest no other state gave"
                );
                seen.push(d);
            }
            std::fs::remove_file(&part).expect("remove part");
            assert_eq!(
                digest(),
                without,
                "removing `.{companion}` restores the digest"
            );
        }
    }

    /// A closure member part that exists but cannot be read is a cache MISS
    /// (no hash for the target), never the hash of an empty file.
    #[test]
    fn test_unreadable_part_is_a_cache_miss() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let (root, char_m) = char_closure(tmp.path());
        assert!(char_hash(&root, &char_m).is_some(), "control: Char hashes");
        // A directory where the private part belongs: it exists, and reading it fails.
        std::fs::create_dir(char_m.with_extension("olean.private")).expect("mkdir part");
        assert_eq!(
            char_hash(&root, &char_m),
            None,
            "an unreadable part must leave the target without a closure hash"
        );
    }

    /// A FINGERPRINT change (kernel/toolchain/heartbeat/elision bump) must re-key
    /// every module's closure hash so nothing stale is reused after a kernel or
    /// toolchain change.
    #[test]
    fn test_fingerprint_change_rekeys_closure_hash() {
        let (src_char, src_init) = stdlib_fixture();
        if !src_char.exists() || !src_init.exists() {
            return;
        }
        let tmp = tempfile::tempdir().expect("tempdir");
        let root = tmp.path().join("root");
        std::fs::create_dir_all(root.join("Init")).expect("mkdir");
        let char_m = root.join("Init/Char.olean");
        let init_m = root.join("Init.olean");
        std::fs::copy(&src_char, &char_m).expect("copy Char");
        std::fs::copy(&src_init, &init_m).expect("copy Init");

        let search: Vec<&Path> = vec![root.as_path()];
        let h_old = compute_closure_hashes(std::slice::from_ref(&char_m), &root, &search, "tc=old")
            .remove(&char_m)
            .expect("hash");
        let h_new = compute_closure_hashes(std::slice::from_ref(&char_m), &root, &search, "tc=new")
            .remove(&char_m)
            .expect("hash");
        assert_ne!(
            h_old, h_new,
            "a fingerprint (e.g. toolchain) change MUST re-key the closure hash"
        );
    }
}
