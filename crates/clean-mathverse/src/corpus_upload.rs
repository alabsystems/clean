// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Corpus upload / publish: push a local Mathverse corpus to a distribution
//! destination (`clean mathverse upload <dir> --to <dest>`).
//!
//! Three destinations, ordered by trust posture:
//!
//! - `release:<tag>` — package the corpus into `mathverse-library-v*.tar.zst`
//!   with a fresh blake3 manifest ([`crate::release::package_release`]) and
//!   publish it as a GitHub Release asset (`gh release create` / `upload
//!   --clobber`). This is the soundest path: the published archive carries the
//!   content-addressed manifest a downloader re-verifies.
//! - `gcs:<bucket/path>` — write a fresh release manifest into the corpus, then
//!   `gcloud storage rsync` (falling back to `gsutil -m rsync`) the shards +
//!   `baseline.mvix` + manifest to a bucket. Byte-for-byte; content-addressing
//!   preserved by the synced `mathverse-manifest.json`.
//! - `server:<url>` — NOT a direct push. `mathverse_serve` holds no signing/auth
//!   key and exposes no bulk-ingest endpoint; minting one would be an
//!   unauthenticated write surface. Server distribution is intentionally
//!   indirect: publish to a release/bucket the server reads
//!   (`$MATHVERSE_CORE_DIR` / `$MATHVERSE_DOWNLOAD_BASE`). This destination
//!   fails closed with that guidance rather than silently succeeding.
//!
//! Every path preserves content-addressing: the published bytes are the exact
//! shard bytes the manifest's blake3 digests cover, so a `clean mathverse
//! download` of the result re-verifies clean.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::MathverseResult;
use crate::release::{io_err, package_release, ReleaseManifest, DEFAULT_CLEAN_RELEASE_REPO};

/// Where to publish a corpus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UploadDest {
    /// A GitHub Release tag (`release:mathverse-v1.3.0`).
    Release { tag: String },
    /// A GCS bucket path (`gcs:my-bucket/mathverse/v1.3.0`).
    Gcs { uri: String },
    /// A running server URL (`server:https://...`) — documented as indirect.
    Server { url: String },
}

impl UploadDest {
    /// Parse a `--to <spec>` value of the form `release:<tag>`, `gcs:<uri>`, or
    /// `server:<url>`.
    ///
    /// # Errors
    /// Fails when the prefix is unknown or the payload after the prefix is empty.
    pub fn parse(spec: &str) -> MathverseResult<Self> {
        let bad = |msg: String| io_err(std::io::ErrorKind::InvalidInput, msg);
        let (scheme, rest) = spec.split_once(':').ok_or_else(|| {
            bad(format!(
                "--to `{spec}` must be `release:<tag>`, `gcs:<bucket/path>`, or `server:<url>`"
            ))
        })?;
        if rest.is_empty() {
            return Err(bad(format!(
                "--to `{spec}` has an empty target after `{scheme}:`"
            )));
        }
        match scheme {
            "release" => Ok(Self::Release {
                tag: rest.to_string(),
            }),
            "gcs" => Ok(Self::Gcs {
                uri: rest.to_string(),
            }),
            "server" => Ok(Self::Server {
                url: rest.to_string(),
            }),
            other => Err(bad(format!(
                "unknown --to scheme `{other}`: use `release:`, `gcs:`, or `server:`"
            ))),
        }
    }
}

/// Inputs for [`upload_corpus`].
#[derive(Clone, Debug)]
pub struct UploadConfig {
    /// Local corpus directory (shards + optional `baseline.mvix` + manifest).
    pub corpus_dir: PathBuf,
    /// Destination.
    pub dest: UploadDest,
    /// Release version embedded in the archive name + manifest.
    pub version: String,
    /// GitHub repo `owner/name` for `release:` publishes.
    pub repo: String,
    /// Staging directory for the packaged archive (`release:` only).
    pub staging_dir: PathBuf,
}

impl UploadConfig {
    /// Construct with the default clean repo + a `dist/` staging dir.
    #[must_use]
    pub fn new(
        corpus_dir: impl Into<PathBuf>,
        dest: UploadDest,
        version: impl Into<String>,
    ) -> Self {
        Self {
            corpus_dir: corpus_dir.into(),
            dest,
            version: version.into(),
            repo: DEFAULT_CLEAN_RELEASE_REPO.to_string(),
            staging_dir: PathBuf::from("dist"),
        }
    }
}

/// Outcome of a successful upload.
#[derive(Clone, Debug)]
pub struct UploadOutcome {
    /// Human-readable destination (e.g. `release:mathverse-v1.3.0`).
    pub destination: String,
    /// The packaged archive path, when one was produced (`release:`).
    pub archive: Option<PathBuf>,
}

/// Publish `cfg.corpus_dir` to `cfg.dest`.
///
/// # Errors
/// Fails if the corpus directory is missing, packaging fails, a required tool
/// (`gh` / `gcloud`) is unavailable, the publish command fails, or the
/// destination is `server:` (which is intentionally indirect).
pub fn upload_corpus(cfg: &UploadConfig) -> MathverseResult<UploadOutcome> {
    if !cfg.corpus_dir.is_dir() {
        return Err(io_err(
            std::io::ErrorKind::NotFound,
            format!("corpus directory not found: {}", cfg.corpus_dir.display()),
        ));
    }
    match &cfg.dest {
        UploadDest::Release { tag } => upload_release(cfg, tag),
        UploadDest::Gcs { uri } => upload_gcs(cfg, uri),
        UploadDest::Server { url } => Err(io_err(
            std::io::ErrorKind::Unsupported,
            format!(
                "server-upload to `{url}` is not a direct push: mathverse_serve holds no \
                 signing/auth key and exposes no bulk-ingest endpoint. Publish to a \
                 release or bucket the server reads instead, e.g.\n  \
                 clean mathverse upload {} --to release:mathverse-v{} --repo {}\n  \
                 clean mathverse upload {} --to gcs:<bucket/path>\nthen point the \
                 server's $MATHVERSE_CORE_DIR / $MATHVERSE_DOWNLOAD_BASE at it.",
                cfg.corpus_dir.display(),
                cfg.version,
                cfg.repo,
                cfg.corpus_dir.display(),
            ),
        )),
    }
}

/// `release:<tag>` — package then publish to a GitHub Release.
fn upload_release(cfg: &UploadConfig, tag: &str) -> MathverseResult<UploadOutcome> {
    let archive = package_release(&cfg.corpus_dir, &cfg.version, &cfg.staging_dir)?;
    let manifest = cfg
        .corpus_dir
        .join(crate::manifest::RELEASE_MANIFEST_FILENAME);
    require_tool("gh", "https://cli.github.com")?;

    // Try to create the release; if it already exists, upload --clobber instead.
    let create = release_create_command(tag, &cfg.repo, &cfg.version, &archive, &manifest);
    if run_ok(create)? {
        return Ok(UploadOutcome {
            destination: format!("release:{tag}"),
            archive: Some(archive),
        });
    }
    let upload = release_upload_command(tag, &cfg.repo, &archive, &manifest);
    if !run_ok(upload)? {
        return Err(io_err(
            std::io::ErrorKind::Other,
            format!(
                "gh release create AND upload --clobber both failed for tag {tag} on {} \
                 (is `gh` authenticated for that repo?)",
                cfg.repo
            ),
        ));
    }
    Ok(UploadOutcome {
        destination: format!("release:{tag}"),
        archive: Some(archive),
    })
}

/// `gcs:<uri>` — write a fresh manifest, then rsync the corpus to the bucket.
fn upload_gcs(cfg: &UploadConfig, uri: &str) -> MathverseResult<UploadOutcome> {
    // Preserve content-addressing: (re)write the release manifest so the synced
    // blake3 digests cover exactly the shard bytes being uploaded.
    let manifest = ReleaseManifest::from_directory(&cfg.corpus_dir, &cfg.version)?;
    manifest.write_to_file(
        &cfg.corpus_dir
            .join(crate::manifest::RELEASE_MANIFEST_FILENAME),
    )?;

    let gs_uri = normalize_gs_uri(uri);
    if have_tool("gcloud") && run_ok(gcloud_rsync_command(&cfg.corpus_dir, &gs_uri))? {
        return Ok(UploadOutcome {
            destination: gs_uri,
            archive: None,
        });
    }
    // Fallback to the legacy gsutil.
    require_tool(
        "gsutil",
        "https://cloud.google.com/storage/docs/gsutil_install",
    )?;
    if !run_ok(gsutil_rsync_command(&cfg.corpus_dir, &gs_uri))? {
        return Err(io_err(
            std::io::ErrorKind::Other,
            format!("gcloud/gsutil rsync to {gs_uri} failed (is gcloud authenticated?)"),
        ));
    }
    Ok(UploadOutcome {
        destination: gs_uri,
        archive: None,
    })
}

/// `gh release create <tag> <archive> <manifest> --repo ... --title ...`.
fn release_create_command(
    tag: &str,
    repo: &str,
    version: &str,
    archive: &Path,
    manifest: &Path,
) -> Command {
    let mut cmd = Command::new("gh");
    cmd.args(["release", "create", tag])
        .arg(archive)
        .arg(manifest)
        .args(["--repo", repo])
        .args(["--title", &format!("Mathverse Library v{version}")])
        .args([
            "--notes",
            "Mathverse Library corpus release (content-addressed; blake3 manifest \
             shipped as mathverse-manifest.json).",
        ]);
    cmd
}

/// `gh release upload <tag> <archive> <manifest> --repo ... --clobber`.
fn release_upload_command(tag: &str, repo: &str, archive: &Path, manifest: &Path) -> Command {
    let mut cmd = Command::new("gh");
    cmd.args(["release", "upload", tag])
        .arg(archive)
        .arg(manifest)
        .args(["--repo", repo])
        .arg("--clobber");
    cmd
}

/// `gcloud storage rsync --recursive <corpus_dir> <gs-uri>`.
fn gcloud_rsync_command(corpus_dir: &Path, gs_uri: &str) -> Command {
    let mut cmd = Command::new("gcloud");
    cmd.args(["storage", "rsync", "--recursive"])
        .arg(corpus_dir)
        .arg(gs_uri);
    cmd
}

/// `gsutil -m rsync -r <corpus_dir> <gs-uri>`.
fn gsutil_rsync_command(corpus_dir: &Path, gs_uri: &str) -> Command {
    let mut cmd = Command::new("gsutil");
    cmd.args(["-m", "rsync", "-r"]).arg(corpus_dir).arg(gs_uri);
    cmd
}

/// Normalize a GCS target to a `gs://` URI (accepts `bucket/path` or `gs://...`).
fn normalize_gs_uri(uri: &str) -> String {
    if uri.starts_with("gs://") {
        uri.to_string()
    } else {
        format!("gs://{}", uri.trim_start_matches('/'))
    }
}

/// Run a command to completion; `Ok(true)` iff it exited 0.
fn run_ok(mut cmd: Command) -> MathverseResult<bool> {
    let status = cmd.status()?;
    Ok(status.success())
}

/// Whether `tool` is invocable (`<tool> --version` spawns).
fn have_tool(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok()
}

/// Require `tool` on PATH or return a typed error with an install hint.
fn require_tool(tool: &str, install_hint: &str) -> MathverseResult<()> {
    if have_tool(tool) {
        Ok(())
    } else {
        Err(io_err(
            std::io::ErrorKind::NotFound,
            format!("required tool `{tool}` not found on PATH — install it ({install_hint})"),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_release_dest() {
        assert_eq!(
            UploadDest::parse("release:mathverse-v1.3.0").expect("parse"),
            UploadDest::Release {
                tag: "mathverse-v1.3.0".to_string()
            }
        );
    }

    #[test]
    fn test_parse_gcs_dest() {
        assert_eq!(
            UploadDest::parse("gcs:bucket/path").expect("parse"),
            UploadDest::Gcs {
                uri: "bucket/path".to_string()
            }
        );
    }

    #[test]
    fn test_parse_server_dest() {
        assert_eq!(
            UploadDest::parse("server:http://localhost:8080").expect("parse"),
            UploadDest::Server {
                url: "http://localhost:8080".to_string()
            }
        );
    }

    #[test]
    fn test_parse_unknown_scheme_errors() {
        let err = UploadDest::parse("ftp:host").expect_err("unknown scheme");
        assert!(err.to_string().contains("unknown --to scheme"));
    }

    #[test]
    fn test_parse_empty_target_errors() {
        let err = UploadDest::parse("release:").expect_err("empty target");
        assert!(err.to_string().contains("empty target"));
    }

    #[test]
    fn test_parse_missing_colon_errors() {
        let err = UploadDest::parse("release").expect_err("missing colon");
        assert!(err.to_string().contains("release:<tag>"));
    }

    #[test]
    fn test_normalize_gs_uri() {
        assert_eq!(normalize_gs_uri("bucket/x"), "gs://bucket/x");
        assert_eq!(normalize_gs_uri("/bucket/x"), "gs://bucket/x");
        assert_eq!(normalize_gs_uri("gs://bucket/x"), "gs://bucket/x");
    }

    #[test]
    fn test_release_create_command_shape() {
        let cmd = release_create_command(
            "mathverse-v1.3.0",
            "alabsystems/clean",
            "1.3.0",
            Path::new("/tmp/a.tar.zst"),
            Path::new("/tmp/mathverse-manifest.json"),
        );
        assert_eq!(cmd.get_program(), "gh");
        let args: Vec<String> = cmd
            .get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        assert_eq!(&args[0..3], &["release", "create", "mathverse-v1.3.0"]);
        assert!(args.iter().any(|a| a == "alabsystems/clean"));
        assert!(args.iter().any(|a| a == "/tmp/a.tar.zst"));
        assert!(args.iter().any(|a| a == "/tmp/mathverse-manifest.json"));
        assert!(args.iter().any(|a| a.contains("Mathverse Library v1.3.0")));
    }

    #[test]
    fn test_gcloud_rsync_command_shape() {
        let cmd = gcloud_rsync_command(Path::new("/corpus"), "gs://b/p");
        assert_eq!(cmd.get_program(), "gcloud");
        let args: Vec<String> = cmd
            .get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        assert_eq!(&args[0..3], &["storage", "rsync", "--recursive"]);
        assert_eq!(args.last().map(String::as_str), Some("gs://b/p"));
    }

    #[test]
    fn test_upload_server_dest_is_documented_error() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cfg = UploadConfig::new(
            dir.path(),
            UploadDest::Server {
                url: "http://x".to_string(),
            },
            "1.3.0",
        );
        let err = upload_corpus(&cfg).expect_err("server upload is indirect");
        let msg = err.to_string();
        assert!(
            msg.contains("--to release:"),
            "must point to release: {msg}"
        );
        assert!(msg.contains("--to gcs:"), "must point to gcs: {msg}");
    }

    #[test]
    fn test_upload_missing_corpus_dir_errors() {
        let cfg = UploadConfig::new(
            "/nonexistent/corpus/dir/xyz",
            UploadDest::Release {
                tag: "t".to_string(),
            },
            "1.3.0",
        );
        let err = upload_corpus(&cfg).expect_err("missing dir");
        assert!(err.to_string().contains("corpus directory not found"));
    }
}
