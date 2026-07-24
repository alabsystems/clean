// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Server-download client: pull a Mathverse corpus from a running
//! `mathverse_serve` instance (`clean mathverse download --from <server-url>`).
//!
//! The existing [`crate::release::download_release`] fetches a corpus from a
//! tagged GitHub Release via `gh`. This module adds the second source the
//! corpus design calls for: a plain HTTP pull from a serve URL. It speaks only
//! the read-only routes the server already exposes:
//!
//! 1. `GET {server}/manifest` — the release manifest (blake3 per shard). When
//!    a server predates the `/manifest` route, it falls back to `GET /shards`
//!    and synthesizes the same manifest from each shard's `content_hash`
//!    (which IS the blake3-over-file-bytes digest, identical to the release
//!    manifest).
//! 2. `GET {server}/download/{stem}` — the raw `.mathverse` bytes per shard.
//!
//! The pulled corpus is landed as a release-shaped directory (shards under
//! their manifest paths plus `mathverse-manifest.json`), then handed to
//! [`crate::release::verify_release`] — the SAME blake3 + `KernelVerified`
//! stamp verification the GitHub-release path uses. A server-download is thus
//! verified by construction; a tampered byte fails the post-download check.
//!
//! The HTTP client is a dependency-light blocking `std::net` GET (the library
//! avoids tokio/reqwest); it follows a single plain-`http` redirect. A redirect
//! to an `https` host (e.g. a GCS signed URL behind `$MATHVERSE_DOWNLOAD_BASE`)
//! is a typed error pointing the operator at the release/bucket directly — the
//! std client does not implement TLS, and the `/manifest` + `/shards` blake3
//! digests are the re-verifiable truth regardless of where bytes are streamed.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::artifacts::ensure_safe_relative_path;
use crate::error::MathverseResult;
use crate::manifest::RELEASE_MANIFEST_FILENAME;
use crate::release::{io_err, ReleaseManifest, VerifyResult};

/// Read timeout for a single server request. Generous: a large shard streamed
/// over a slow link must not trip it, but a wedged socket must not hang forever.
const READ_TIMEOUT: Duration = Duration::from_secs(120);

/// Maximum redirects followed for one request (server may 302 to a download base).
const MAX_REDIRECTS: u8 = 3;

/// Where to pull a corpus from and where to land it.
#[derive(Clone, Debug)]
pub struct ServerDownloadConfig {
    /// Base URL of a running `mathverse_serve` (e.g. `http://127.0.0.1:8080`).
    pub server_url: String,
    /// Output directory for the verified, release-shaped corpus.
    pub out_dir: PathBuf,
}

/// Pull every shard + the release manifest from `cfg.server_url`, land them in
/// `cfg.out_dir`, then blake3-verify the result against the manifest.
///
/// # Errors
/// Fails if the server is unreachable, the manifest cannot be fetched/parsed, a
/// shard download fails, a manifest path is unsafe, or the post-download
/// verification reports any mismatch / missing shard.
pub fn download_from_server(cfg: &ServerDownloadConfig) -> MathverseResult<VerifyResult> {
    let base = cfg.server_url.trim_end_matches('/').to_string();
    std::fs::create_dir_all(&cfg.out_dir)?;

    // 1. Fetch (or synthesize) the release manifest and persist it so the
    //    re-verify step reads the SAME digests the server published.
    let manifest = fetch_manifest(&base)?;
    let manifest_path = cfg.out_dir.join(RELEASE_MANIFEST_FILENAME);
    manifest.write_to_file(&manifest_path)?;

    if manifest.shards.is_empty() {
        return Err(io_err(
            std::io::ErrorKind::InvalidData,
            format!("server {base} reports an empty corpus (0 shards) — nothing to download"),
        ));
    }

    // 2. Pull each shard by its manifest stem into its manifest-relative path.
    for entry in &manifest.shards {
        ensure_safe_relative_path(&entry.path)?;
        let stem = shard_stem(&entry.path);
        let url = format!("{base}/download/{stem}");
        let resp = http_get(&url)?;
        if resp.status != 200 {
            return Err(io_err(
                std::io::ErrorKind::Other,
                format!(
                    "GET {url} returned HTTP {} (expected 200 octet-stream shard bytes)",
                    resp.status
                ),
            ));
        }
        let dest = cfg.out_dir.join(&entry.path);
        if let Some(parent) = dest.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&dest, &resp.body)?;
    }

    // 3. Re-verify the landed corpus (blake3 each shard vs manifest + honor any
    //    KernelVerified stamp). This is the SAME path the gh-release download
    //    uses; a server-download is verified by construction.
    let result = crate::release::verify_release(&cfg.out_dir)?;
    if !result.is_ok() {
        return Err(io_err(
            std::io::ErrorKind::InvalidData,
            format!(
                "post-download verification FAILED for {}: {} mismatch(es), {} missing shard(s)",
                cfg.out_dir.display(),
                result.failures.len(),
                result.missing.len()
            ),
        ));
    }
    Ok(result)
}

/// Fetch `GET /manifest`; on a non-200 (older server without the route), fall
/// back to `GET /shards` and synthesize the manifest from each shard's blake3
/// `content_hash`.
fn fetch_manifest(base: &str) -> MathverseResult<ReleaseManifest> {
    let resp = http_get(&format!("{base}/manifest"))?;
    if resp.status == 200 {
        if let Ok(m) = ReleaseManifest::from_json(&String::from_utf8_lossy(&resp.body)) {
            return Ok(m);
        }
    }
    // Fallback: derive the manifest from /shards (content_hash == blake3).
    let shards = http_get(&format!("{base}/shards"))?;
    if shards.status != 200 {
        return Err(io_err(
            std::io::ErrorKind::NotFound,
            format!(
                "server {base} has neither a usable /manifest nor /shards route \
                 (got HTTP {} from /shards) — is it a mathverse_serve instance?",
                shards.status
            ),
        ));
    }
    manifest_from_shards_json(&shards.body)
}

/// Build a [`ReleaseManifest`] from a `GET /shards` JSON payload.
fn manifest_from_shards_json(body: &[u8]) -> MathverseResult<ReleaseManifest> {
    let value: serde_json::Value = serde_json::from_slice(body)?;
    let arr = value
        .get("shards")
        .and_then(|s| s.as_array())
        .ok_or_else(|| {
            io_err(
                std::io::ErrorKind::InvalidData,
                "/shards payload has no `shards` array".to_string(),
            )
        })?;
    let json = serde_json::json!({
        "manifest_version": 1,
        "release_version": "server-pull",
        "created_at": "unknown",
        "total_shards": arr.len(),
        "total_bytes": arr.iter().filter_map(|s| s.get("size_bytes").and_then(|v| v.as_u64())).sum::<u64>(),
        "shards": arr.iter().map(|s| serde_json::json!({
            "path": s.get("path").and_then(|v| v.as_str()).unwrap_or_default(),
            "size": s.get("size_bytes").and_then(|v| v.as_u64()).unwrap_or(0),
            "blake3": s.get("content_hash").and_then(|v| v.as_str()).unwrap_or_default(),
        })).collect::<Vec<_>>(),
    });
    ReleaseManifest::from_json(&json.to_string())
}

/// A parsed HTTP response: status code + body bytes.
struct HttpResponse {
    status: u16,
    body: Vec<u8>,
}

/// Blocking HTTP/1.1 GET over `std::net`, following up to [`MAX_REDIRECTS`]
/// plain-`http` redirects. `https` redirects are a typed error (no TLS in the
/// std client).
fn http_get(url: &str) -> MathverseResult<HttpResponse> {
    let mut current = url.to_string();
    for _ in 0..=MAX_REDIRECTS {
        let (host, port, target) = parse_http_url(&current)?;
        let raw = http_get_once(&host, port, &target)?;
        let status = parse_status(&raw)?;
        let header_end = find_header_end(&raw).ok_or_else(|| {
            io_err(
                std::io::ErrorKind::InvalidData,
                format!("malformed HTTP response from {current} (no header terminator)"),
            )
        })?;
        if matches!(status, 301 | 302 | 303 | 307 | 308) {
            let location = header_value(&raw[..header_end], "location").ok_or_else(|| {
                io_err(
                    std::io::ErrorKind::InvalidData,
                    format!("{current} returned HTTP {status} without a Location header"),
                )
            })?;
            current = absolutize(&current, &location);
            continue;
        }
        return Ok(HttpResponse {
            status,
            body: raw[header_end..].to_vec(),
        });
    }
    Err(io_err(
        std::io::ErrorKind::Other,
        format!("too many redirects following {url}"),
    ))
}

/// One request/response round-trip; returns the full raw response bytes.
fn http_get_once(host: &str, port: u16, target: &str) -> MathverseResult<Vec<u8>> {
    let mut stream = TcpStream::connect((host, port)).map_err(|e| {
        io_err(
            e.kind(),
            format!("cannot connect to {host}:{port}: {e} — is `mathverse_serve` running there?"),
        )
    })?;
    stream.set_read_timeout(Some(READ_TIMEOUT))?;
    stream.set_write_timeout(Some(READ_TIMEOUT))?;
    let request = format!(
        "GET {target} HTTP/1.1\r\nHost: {host}:{port}\r\nUser-Agent: clean-mathverse/download\r\nAccept: */*\r\nConnection: close\r\n\r\n"
    );
    stream.write_all(request.as_bytes())?;
    stream.flush()?;
    let mut buf = Vec::new();
    stream.read_to_end(&mut buf)?;
    Ok(buf)
}

/// Split a plain-`http` URL into `(host, port, request-target)`.
fn parse_http_url(url: &str) -> MathverseResult<(String, u16, String)> {
    if let Some(rest) = url.strip_prefix("https://") {
        return Err(io_err(
            std::io::ErrorKind::Unsupported,
            format!(
                "https URL `{rest}` is not supported by the built-in download client \
                 (no TLS): the server is redirecting shard bytes to an https host \
                 (e.g. $MATHVERSE_DOWNLOAD_BASE / a GCS signed URL). Fetch that \
                 release/bucket directly, or point --from at a server running in \
                 local-stream mode (no MATHVERSE_DOWNLOAD_BASE)."
            ),
        ));
    }
    let rest = url.strip_prefix("http://").ok_or_else(|| {
        io_err(
            std::io::ErrorKind::InvalidInput,
            format!("--from URL must start with http:// (got `{url}`)"),
        )
    })?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => {
            let port = p.parse::<u16>().map_err(|_| {
                io_err(
                    std::io::ErrorKind::InvalidInput,
                    format!("invalid port in URL `{url}`"),
                )
            })?;
            (h.to_string(), port)
        }
        None => (authority.to_string(), 80),
    };
    if host.is_empty() {
        return Err(io_err(
            std::io::ErrorKind::InvalidInput,
            format!("URL `{url}` has no host"),
        ));
    }
    let target = if path.is_empty() {
        "/".to_string()
    } else {
        path.to_string()
    };
    Ok((host, port, target))
}

/// Resolve a (possibly relative) redirect `location` against the `current` URL.
fn absolutize(current: &str, location: &str) -> String {
    if location.starts_with("http://") || location.starts_with("https://") {
        return location.to_string();
    }
    // Relative redirect: keep scheme://authority, replace the path.
    let scheme_end = current.find("://").map(|i| i + 3).unwrap_or(0);
    let authority_end = current[scheme_end..]
        .find('/')
        .map(|i| scheme_end + i)
        .unwrap_or(current.len());
    let origin = &current[..authority_end];
    if location.starts_with('/') {
        format!("{origin}{location}")
    } else {
        format!("{origin}/{location}")
    }
}

/// Parse the status code from a raw HTTP response (`HTTP/1.1 200 OK`).
fn parse_status(raw: &[u8]) -> MathverseResult<u16> {
    let line_end = raw
        .windows(2)
        .position(|w| w == b"\r\n")
        .unwrap_or(raw.len());
    let line = String::from_utf8_lossy(&raw[..line_end]);
    line.split_whitespace()
        .nth(1)
        .and_then(|c| c.parse::<u16>().ok())
        .ok_or_else(|| {
            io_err(
                std::io::ErrorKind::InvalidData,
                format!("could not parse HTTP status line: `{line}`"),
            )
        })
}

/// Byte offset just past the `\r\n\r\n` header terminator.
fn find_header_end(raw: &[u8]) -> Option<usize> {
    raw.windows(4).position(|w| w == b"\r\n\r\n").map(|p| p + 4)
}

/// Case-insensitive header lookup over the header block.
fn header_value(header_block: &[u8], name: &str) -> Option<String> {
    let text = String::from_utf8_lossy(header_block);
    for line in text.lines() {
        if let Some((k, v)) = line.split_once(':') {
            if k.trim().eq_ignore_ascii_case(name) {
                return Some(v.trim().to_string());
            }
        }
    }
    None
}

/// The `/download/{stem}` key for a manifest shard path (`base/lean4.mathverse`
/// -> `lean4`), matching the server's `resolve_shard_path` keying.
fn shard_stem(path: &str) -> String {
    Path::new(path)
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_http_url_with_port_and_path() {
        let (h, p, t) = parse_http_url("http://127.0.0.1:8080/manifest").expect("parse");
        assert_eq!(h, "127.0.0.1");
        assert_eq!(p, 8080);
        assert_eq!(t, "/manifest");
    }

    #[test]
    fn test_parse_http_url_default_port_and_root() {
        let (h, p, t) = parse_http_url("http://example.org").expect("parse");
        assert_eq!(h, "example.org");
        assert_eq!(p, 80);
        assert_eq!(t, "/");
    }

    #[test]
    fn test_parse_http_url_https_is_rejected_with_hint() {
        let err = parse_http_url("https://storage.googleapis.com/x").expect_err("https rejected");
        assert!(err.to_string().contains("https"));
        assert!(err.to_string().contains("TLS"));
    }

    #[test]
    fn test_parse_status_line() {
        assert_eq!(
            parse_status(b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n\r\nabc").expect("status"),
            200
        );
        assert_eq!(
            parse_status(b"HTTP/1.1 404 Not Found\r\n\r\n").expect("status"),
            404
        );
    }

    #[test]
    fn test_header_value_case_insensitive() {
        let block = b"HTTP/1.1 302 Found\r\nLocation: http://x/y\r\nConnection: close\r\n\r\n";
        assert_eq!(
            header_value(&block[..], "location").as_deref(),
            Some("http://x/y")
        );
    }

    #[test]
    fn test_shard_stem_strips_dir_and_ext() {
        assert_eq!(shard_stem("base/lean4_stdlib.mathverse"), "lean4_stdlib");
        assert_eq!(shard_stem("acl2.mathverse"), "acl2");
    }

    #[test]
    fn test_absolutize_relative_and_absolute() {
        assert_eq!(
            absolutize("http://h:8080/download/x", "/other"),
            "http://h:8080/other"
        );
        assert_eq!(absolutize("http://h:8080/a", "http://z/b"), "http://z/b");
    }

    #[test]
    fn test_manifest_from_shards_json() {
        let body =
            br#"{"shards":[{"path":"base/a.mathverse","content_hash":"aa","size_bytes":7}]}"#;
        let m = manifest_from_shards_json(body).expect("synthesize");
        assert_eq!(m.shards.len(), 1);
        assert_eq!(m.shards[0].path, "base/a.mathverse");
        assert_eq!(m.shards[0].blake3, "aa");
        assert_eq!(m.shards[0].size, 7);
    }
}
