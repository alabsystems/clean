// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the corpus UPLOAD / DOWNLOAD / SERVE verbs.
//!
//! - offline upload->download round-trip: `package_release` (UPLOAD packaging)
//!   -> `extract_archive` (DOWNLOAD unpack) -> `verify_release` proves the
//!   blake3 manifest digests survive packaging byte-for-byte;
//! - upload destination parsing + the `server:` indirect-publish guard;
//! - the server-download client (`download_from_server`) against the REAL
//!   `mathverse_serve` binary over a self-contained fixture Core: serve on an
//!   ephemeral port -> pull /manifest + each shard -> verify -> a `/search`
//!   returns a hit. This also exercises the new `GET /manifest` route and its
//!   synthesize-from-loader-manifest path.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_mathverse::artifacts::extract_archive;
use clean_mathverse::corpus_download::{download_from_server, ServerDownloadConfig};
use clean_mathverse::corpus_upload::{upload_corpus, UploadConfig, UploadDest};
use clean_mathverse::manifest::LibraryLoader;
use clean_mathverse::release::{package_release, verify_release, ReleaseManifest};
use clean_mathverse::shard::ShardWriter;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
};

// ---------------------------------------------------------------------------
// Offline upload -> download round-trip (blake3 preserved)
// ---------------------------------------------------------------------------

#[test]
fn upload_package_then_download_extract_blake3_matches() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let corpus = tmp.path().join("corpus");
    let base = corpus.join("base");
    std::fs::create_dir_all(&base).expect("mkdir base");
    std::fs::write(
        base.join("alpha.mathverse"),
        b"alpha-shard-bytes-0123456789",
    )
    .expect("write");
    std::fs::write(base.join("beta.mathverse"), b"beta-shard-bytes-abcdefghij").expect("write");

    // UPLOAD side: package into a content-addressed archive + manifest.
    let staging = tmp.path().join("dist");
    let archive = package_release(&corpus, "0.0.1-test", &staging).expect("package");
    assert!(archive.exists(), "archive must be created");

    // DOWNLOAD side: extract the archive into a fresh dir and re-verify.
    let extracted = tmp.path().join("extracted");
    extract_archive(&archive, &extracted, 1).expect("extract");
    let result = verify_release(&extracted).expect("verify");
    assert!(
        result.is_ok(),
        "round-trip blake3 must match: {} checked, {} failures, {} missing",
        result.checked,
        result.failures.len(),
        result.missing.len()
    );
    assert_eq!(result.passed, 2, "both shards must verify");

    // The shipped manifest digests must equal a fresh hash of the extracted bytes.
    let manifest =
        ReleaseManifest::from_file(&extracted.join("mathverse-manifest.json")).expect("manifest");
    for entry in &manifest.shards {
        let bytes = std::fs::read(extracted.join(&entry.path)).expect("read shard");
        assert_eq!(
            blake3::hash(&bytes).to_hex().to_string(),
            entry.blake3,
            "shard {} blake3 must match manifest",
            entry.path
        );
    }
}

// ---------------------------------------------------------------------------
// Upload destination parsing + the server-indirect guard
// ---------------------------------------------------------------------------

#[test]
fn upload_dest_parsing() {
    assert_eq!(
        UploadDest::parse("release:mathverse-v1.3.0").expect("release"),
        UploadDest::Release {
            tag: "mathverse-v1.3.0".to_string()
        }
    );
    assert_eq!(
        UploadDest::parse("gcs:bucket/path").expect("gcs"),
        UploadDest::Gcs {
            uri: "bucket/path".to_string()
        }
    );
    UploadDest::parse("nope:x").expect_err("unknown scheme must error");
}

#[test]
fn upload_to_server_is_indirect_guard() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let cfg = UploadConfig::new(
        tmp.path(),
        UploadDest::Server {
            url: "http://localhost:8080".to_string(),
        },
        "1.3.0",
    );
    let err = upload_corpus(&cfg).expect_err("server upload is indirect");
    let msg = err.to_string();
    assert!(
        msg.contains("--to release:") && msg.contains("--to gcs:"),
        "guidance: {msg}"
    );
}

// ---------------------------------------------------------------------------
// Server-download client against the REAL mathverse_serve
// ---------------------------------------------------------------------------

#[test]
fn serve_then_download_from_server_then_search_returns() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let core = tmp.path().join("core");
    build_fixture_core(&core);

    let handle = start_service(&core);

    // (a) /manifest is reachable and lists the fixture shard (synthesize path).
    let manifest = get(handle.port, "/manifest").json();
    assert!(
        manifest["shards"]
            .as_array()
            .map(|a| !a.is_empty())
            .unwrap_or(false),
        "/manifest must list >=1 shard: {manifest}"
    );

    // (b) DOWNLOAD from the server, then verify (blake3 by construction).
    let out = tmp.path().join("downloaded");
    let result = download_from_server(&ServerDownloadConfig {
        server_url: format!("http://127.0.0.1:{}", handle.port),
        out_dir: out.clone(),
    })
    .expect("download from server");
    assert!(result.is_ok(), "server download must verify clean");
    assert!(
        out.join("base/test_core.mathverse").exists(),
        "downloaded shard must be on disk"
    );

    // (c) a /search returns at least one declaration.
    let search = get(handle.port, "/search?limit=5").json();
    assert!(
        search["count"].as_u64().unwrap_or(0) > 0,
        "a search must return at least one hit: {search}"
    );
}

// ---------------------------------------------------------------------------
// Helpers (mirroring tests/serve_endpoints.rs conventions)
// ---------------------------------------------------------------------------

/// Build a 3-declaration Core fixture (real, loadable shard + manifest).
fn build_fixture_core(dir: &Path) {
    let loader = LibraryLoader::new(dir.to_path_buf());
    loader.init().expect("init core dir");

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let ty = writer.add_expr(FlatExpr::sort(l0));

    let decls: &[(&str, ImportConfidence, ContentDomain, AxiomProfile)] = &[
        (
            "Test.kernel_thm",
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "Test.kernel_def",
            ImportConfidence::KernelVerified,
            ContentDomain::Logic,
            AxiomProfile::NONE,
        ),
        (
            "Test.choice_user",
            ImportConfidence::Axiomatized,
            ContentDomain::PureMath,
            AxiomProfile::CHOICE,
        ),
    ];

    for &(name, conf, domain, profile) in decls {
        let ni = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: ty,
            value_idx: ty,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: conf as u8,
            content_domain: domain as u8,
            decl_kind: 0,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }

    loader
        .write_shard(&writer, "test_core", false)
        .expect("write fixture shard");
}

fn free_port() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral");
    let port = listener.local_addr().expect("local addr").port();
    drop(listener);
    port
}

struct ServeHandle {
    child: Child,
    port: u16,
}

impl Drop for ServeHandle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Start the real `mathverse_serve` over `core_dir` on a free port and wait for
/// `/healthz`.
fn start_service(core_dir: &Path) -> ServeHandle {
    let port = free_port();
    let child = Command::new(PathBuf::from(env!("CARGO_BIN_EXE_mathverse_serve")))
        .env("PORT", port.to_string())
        .env("MATHVERSE_CORE_DIR", core_dir)
        .env_remove("MATHVERSE_DOWNLOAD_BASE")
        .spawn()
        .expect("spawn mathverse_serve");
    let handle = ServeHandle { child, port };

    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Ok(resp) = try_get(port, "/healthz") {
            if resp.status == 200 {
                break;
            }
        }
        assert!(
            Instant::now() < deadline,
            "service did not become healthy within 30s"
        );
        std::thread::sleep(Duration::from_millis(100));
    }
    handle
}

struct HttpResponse {
    status: u16,
    body: Vec<u8>,
}

impl HttpResponse {
    fn json(&self) -> serde_json::Value {
        serde_json::from_slice(&self.body).expect("response body is valid JSON")
    }
}

fn try_get(port: u16, path: &str) -> std::io::Result<HttpResponse> {
    let mut stream = TcpStream::connect(("127.0.0.1", port))?;
    stream.set_read_timeout(Some(Duration::from_secs(10)))?;
    let req = format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes())?;
    let mut raw = Vec::new();
    stream.read_to_end(&mut raw)?;

    let split = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("response has header terminator");
    let head = String::from_utf8_lossy(&raw[..split]).into_owned();
    let body = raw[split + 4..].to_vec();
    let status = head
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|code| code.parse::<u16>().ok())
        .expect("parse status code");
    Ok(HttpResponse { status, body })
}

fn get(port: u16, path: &str) -> HttpResponse {
    try_get(port, path).expect("GET request")
}
