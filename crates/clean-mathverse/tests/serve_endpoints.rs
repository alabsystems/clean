// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the `mathverse_serve` Cloud Run distribution
//! front-end.
//!
//! Builds a tiny verified Core fixture (a 3-declaration `.mathverse` shard plus
//! its manifest), starts the real `mathverse_serve` binary on a free port, and
//! hits every endpoint over a raw HTTP/1.1 client. Assertions check both
//! correctness (stats counts match, `/theorem` resolves, `/search` finds a
//! known name, `/download` streams the shard bytes) and the Phase-1 honesty
//! contract (the trust note appears; the service never overclaims).

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_mathverse::manifest::LibraryLoader;
use clean_mathverse::shard::ShardWriter;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
};

/// Build a 3-declaration Core fixture under `dir`. Returns the names written.
fn build_fixture_core(dir: &Path) -> Vec<String> {
    let loader = LibraryLoader::new(dir.to_path_buf());
    loader.init().expect("init core dir");

    let mut writer = ShardWriter::new();
    // A reconstructable type: `Sort 0` (Prop). Reconstructs cleanly so the
    // service can compute an `expr_canonical_digest` for it.
    let l0 = writer.add_level(FlatLevel::zero());
    let ty = writer.add_expr(FlatExpr::sort(l0));

    // Three decls spanning two trust tiers so /stats has a real breakdown:
    // two KernelVerified (axiom-free) and one Axiomatized carrying CHOICE.
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

    decls.iter().map(|d| d.0.to_string()).collect()
}

/// Grab a free TCP port by binding to port 0 and reading back the assignment.
fn free_port() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind ephemeral");
    let port = listener.local_addr().expect("local addr").port();
    drop(listener);
    port
}

/// Path to the binary under test (provided by cargo for integration tests).
fn serve_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_mathverse_serve"))
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

/// Start the service over `core_dir` on a free port and wait for `/healthz`.
fn start_service(core_dir: &Path, download_base: Option<&str>) -> ServeHandle {
    start_service_with(core_dir, download_base, None, None)
}

/// Start the service, optionally pointing `$MATHVERSE_VERDICTS_DIR` at a
/// re-auditor output directory (Phase-2 `/verdict` + `/audit`) and
/// `$MATHVERSE_SUBMIT_QUEUE` at a submission queue (Phase-2.1 `POST /submit` +
/// `GET /submit/{id}`).
fn start_service_with(
    core_dir: &Path,
    download_base: Option<&str>,
    verdicts_dir: Option<&Path>,
    submit_queue_dir: Option<&Path>,
) -> ServeHandle {
    let port = free_port();
    let mut cmd = Command::new(serve_bin());
    cmd.env("PORT", port.to_string())
        .env("MATHVERSE_CORE_DIR", core_dir);
    if let Some(base) = download_base {
        cmd.env("MATHVERSE_DOWNLOAD_BASE", base);
    } else {
        cmd.env_remove("MATHVERSE_DOWNLOAD_BASE");
    }
    if let Some(vd) = verdicts_dir {
        cmd.env("MATHVERSE_VERDICTS_DIR", vd);
    } else {
        cmd.env_remove("MATHVERSE_VERDICTS_DIR");
    }
    if let Some(q) = submit_queue_dir {
        cmd.env("MATHVERSE_SUBMIT_QUEUE", q);
    } else {
        cmd.env_remove("MATHVERSE_SUBMIT_QUEUE");
    }
    let child = cmd.spawn().expect("spawn mathverse_serve");
    let handle = ServeHandle { child, port };

    // Poll /healthz until the listener is up (load + bind takes a moment).
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Ok(resp) = try_get(port, "/healthz") {
            if resp.status == 200 && resp.body_text() == "ok" {
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
    fn body_text(&self) -> String {
        String::from_utf8_lossy(&self.body).into_owned()
    }
    fn json(&self) -> serde_json::Value {
        serde_json::from_slice(&self.body).expect("response body is valid JSON")
    }
}

/// Minimal blocking HTTP/1.1 GET client (no reqwest dependency needed offline).
fn try_get(port: u16, path: &str) -> std::io::Result<HttpResponse> {
    let mut stream = TcpStream::connect(("127.0.0.1", port))?;
    stream.set_read_timeout(Some(Duration::from_secs(10)))?;
    let req = format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes())?;
    let mut raw = Vec::new();
    stream.read_to_end(&mut raw)?;

    // Split head / body on the first CRLFCRLF.
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

/// Minimal blocking HTTP/1.1 POST client with the given request body — used to
/// drive the Phase-2.1 `POST /submit` live path.
fn post_body(port: u16, path: &str, body: &[u8]) -> HttpResponse {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).expect("connect");
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .expect("timeout");
    let mut req = format!(
        "POST {path} HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    )
    .into_bytes();
    req.extend_from_slice(body);
    stream.write_all(&req).expect("write");
    let mut raw = Vec::new();
    stream.read_to_end(&mut raw).expect("read");
    let split = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("header terminator");
    let head = String::from_utf8_lossy(&raw[..split]).into_owned();
    let resp_body = raw[split + 4..].to_vec();
    let status = head
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|c| c.parse::<u16>().ok())
        .expect("status");
    HttpResponse {
        status,
        body: resp_body,
    }
}

/// Like `get`, but does not follow redirects — returns the raw head so a
/// `Location` header can be asserted.
fn get_head(port: u16, path: &str) -> (u16, String) {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).expect("connect");
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .expect("timeout");
    let req = format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes()).expect("write");
    let mut raw = Vec::new();
    stream.read_to_end(&mut raw).expect("read");
    let split = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("header terminator");
    let head = String::from_utf8_lossy(&raw[..split]).into_owned();
    let status = head
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|c| c.parse::<u16>().ok())
        .expect("status");
    (status, head)
}

#[test]
fn test_serve_endpoints_correct_and_honest() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let names = build_fixture_core(tmp.path());
    let service = start_service(tmp.path(), None);
    let port = service.port;

    // -- /healthz ---------------------------------------------------------
    let health = get(port, "/healthz");
    assert_eq!(health.status, 200, "healthz status");
    assert_eq!(health.body_text(), "ok", "healthz body");

    // -- /stats -----------------------------------------------------------
    let stats = get(port, "/stats");
    assert_eq!(stats.status, 200, "stats status");
    let stats_json = stats.json();
    assert_eq!(
        stats_json["total_declarations"].as_u64(),
        Some(3),
        "stats total matches fixture decl count"
    );
    assert_eq!(
        stats_json["shard_count"].as_u64(),
        Some(1),
        "stats shard count matches fixture"
    );
    // Two KernelVerified, one Axiomatized.
    assert_eq!(
        stats_json["by_trust_level"]["KernelVerified"].as_u64(),
        Some(2),
        "two kernel-verified decls"
    );
    assert_eq!(
        stats_json["by_trust_level"]["Axiomatized"].as_u64(),
        Some(1),
        "one axiomatized decl"
    );
    // Honesty: independently_reverifiable counts ONLY the kernel tier, and the
    // trust note is present and disclaims trust-authority status.
    assert_eq!(
        stats_json["independently_reverifiable"]["count"].as_u64(),
        Some(2),
        "only kernel-verified is independently re-verifiable"
    );
    assert_eq!(
        stats_json["independently_reverifiable"]["self_attested"].as_u64(),
        Some(1),
        "the axiomatized decl is self-attested"
    );
    let note = stats_json["trust_note"].as_str().unwrap_or("");
    assert!(
        note.contains("distribution front-end") && note.contains("not a trust authority"),
        "stats carries the honest trust note, got: {note}"
    );

    // -- /search ----------------------------------------------------------
    let search = get(port, "/search?q=kernel_thm");
    assert_eq!(search.status, 200, "search status");
    let search_json = search.json();
    assert_eq!(
        search_json["count"].as_u64(),
        Some(1),
        "search finds exactly the one matching name"
    );
    let hit = &search_json["results"][0];
    assert_eq!(hit["name"].as_str(), Some("Test.kernel_thm"));
    assert_eq!(
        hit["trust_level"].as_str(),
        Some("KernelVerified"),
        "search reports the stored trust level"
    );
    assert!(
        hit["expr_canonical_digest"].as_str().is_some(),
        "search surfaces the content digest for re-verification"
    );

    // Axiom filter: only the CHOICE-carrying decl matches.
    let by_axiom = get(port, "/search?axiom=CHOICE");
    let by_axiom_json = by_axiom.json();
    assert_eq!(
        by_axiom_json["count"].as_u64(),
        Some(1),
        "axiom=CHOICE matches exactly the choice user"
    );
    assert_eq!(
        by_axiom_json["results"][0]["name"].as_str(),
        Some("Test.choice_user")
    );

    // Domain filter: two PureMath decls.
    let by_domain = get(port, "/search?domain=PureMath");
    assert_eq!(
        by_domain.json()["count"].as_u64(),
        Some(2),
        "domain=PureMath matches both pure-math decls"
    );

    // -- /theorem/{name} --------------------------------------------------
    let thm = get(port, "/theorem/Test.choice_user");
    assert_eq!(thm.status, 200, "theorem status");
    let thm_json = thm.json();
    assert_eq!(thm_json["name"].as_str(), Some("Test.choice_user"));
    assert_eq!(
        thm_json["trust_level"].as_str(),
        Some("Axiomatized"),
        "theorem returns the stored trust level"
    );
    // Honesty: the CHOICE decl is foundational (within the foundational closure)
    // but NOT axiom-free, and the named axiom is surfaced.
    assert_eq!(
        thm_json["axiom_profile"]["axiom_count"].as_u64(),
        Some(1),
        "one axiom bit set"
    );
    let named = thm_json["axiom_profile"]["named_axioms"]
        .as_array()
        .expect("named_axioms array");
    assert!(
        named.iter().any(|n| n.as_str() == Some("CHOICE")),
        "CHOICE is surfaced in named_axioms"
    );
    assert!(
        thm_json["expr_canonical_digest"].as_str().is_some(),
        "theorem surfaces the canonical digest"
    );
    assert!(
        thm_json["trust_note"]
            .as_str()
            .unwrap_or("")
            .contains("not a trust authority"),
        "theorem carries the honest trust note"
    );

    // The kernel-verified decl is axiom-free + foundational.
    let kthm = get(port, "/theorem/Test.kernel_thm").json();
    assert_eq!(kthm["axiom_profile"]["axiom_count"].as_u64(), Some(0));
    assert_eq!(kthm["axiom_profile"]["foundational"].as_bool(), Some(true));

    // Missing theorem -> 404.
    let missing = get(port, "/theorem/Does.Not.Exist");
    assert_eq!(missing.status, 404, "unknown theorem is 404");

    // -- /shards ----------------------------------------------------------
    let shards = get(port, "/shards");
    assert_eq!(shards.status, 200, "shards status");
    let shards_json = shards.json();
    assert_eq!(shards_json["shard_count"].as_u64(), Some(1));
    let shard0 = &shards_json["shards"][0];
    assert_eq!(
        shard0["declaration_count"].as_u64(),
        Some(3),
        "shard reports 3 declarations"
    );
    assert!(
        shard0["size_bytes"].as_u64().unwrap_or(0) > 0,
        "shard reports a nonzero on-disk size"
    );
    let shard_key = shard0["shard"].as_str().expect("shard key").to_string();
    assert_eq!(shard_key, "test_core", "shard key is the file stem");

    // -- /download/{shard} (stream local) --------------------------------
    let download = get(port, &format!("/download/{shard_key}"));
    assert_eq!(download.status, 200, "download status");
    assert!(
        download.body.len() > 64,
        "download streams the shard bytes (got {} bytes)",
        download.body.len()
    );
    // The bytes should match the on-disk shard exactly.
    let on_disk = std::fs::read(tmp.path().join("base/test_core.mathverse")).expect("read shard");
    assert_eq!(
        download.body, on_disk,
        "streamed download equals the on-disk shard"
    );

    // Unknown shard -> 404.
    let bad_dl = get(port, "/download/nope");
    assert_eq!(bad_dl.status, 404, "unknown shard download is 404");

    // -- method guard -----------------------------------------------------
    // (All names should be discoverable; sanity-check the fixture set.)
    assert_eq!(names.len(), 3);

    drop(service);
}

#[test]
fn test_serve_download_redirect_mode() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let _names = build_fixture_core(tmp.path());
    let base = "https://example-bucket.test/mathverse";
    let service = start_service(tmp.path(), Some(base));
    let port = service.port;

    // In redirect mode, /download/{shard} 302s to {base}/{rel-path} instead of
    // streaming bytes — the GCS signed-URL serving path.
    let (status, head) = get_head(port, "/download/test_core");
    assert_eq!(status, 302, "redirect mode returns 302");
    assert!(
        head.contains(&format!("Location: {base}/base/test_core.mathverse")),
        "redirect points at the configured download base, got head:\n{head}"
    );

    drop(service);
}

// === Phase-2 trust-surface endpoints (/verdict, /audit, /submit) ===========

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use clean_mathverse::trust_sign::{
    attest, Ed25519LocalBackend, RevocationEntry, RevocationList, RevocationReason, SignedVerdict,
    Submission,
};

/// `fun (p : Prop) (h : p) => h : ∀ (p : Prop), p → p` under `name` — a
/// foundational-only theorem the kernel re-checks (matching the trust-core's
/// own fixture). Re-attesting it yields a genuine `KernelVerified`.
fn imp_self_theorem(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
    }
}

/// `fun (p q : Prop) (hp : p) (_ : q) => hp : ∀ (p q : Prop), p → q → p` — a
/// second foundational-only theorem with a DISTINCT statement digest (so it is
/// independently revocable without touching `imp_self`'s digest).
fn const_proj_theorem(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3)),
                ),
            ),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
                ),
            ),
        ),
    }
}

/// Build a re-auditor output directory under `dir`: a `verdicts/` folder with
/// two GENUINELY re-attested `KernelVerified` verdicts (one of which we then
/// revoke), plus a signed revocation list. Returns
/// `(live_name, revoked_name, revoked_digest)`.
///
/// The verdicts are produced via the real attestation bridge (`attest` →
/// `recheck_and_classify`) and signed with a real Ed25519 keypair — exactly the
/// path the `mathverse_reauditor` binary uses. The service only ever READS them.
fn build_reauditor_output(dir: &Path) -> (String, String, String) {
    let (backend, _secret) =
        Ed25519LocalBackend::generate("ed25519-local:test").expect("ed25519 keypair");
    let verdicts = dir.join("verdicts");
    std::fs::create_dir_all(&verdicts).expect("verdicts dir");

    // Re-attest each theorem in its OWN fresh environment (the re-auditor's
    // contract) and sign the resulting verdict.
    let sign_and_write = |decl: Declaration, name: &str| -> String {
        let mut env = Environment::new();
        let att = attest(&mut env, decl, "test-commit").expect("attest");
        assert!(att.foundational, "the fixture theorem is foundational");
        let mut signed = SignedVerdict::from_attestation(&att, "2026-06-24T00:00:00Z".to_string());
        signed.sign_with(&backend).expect("sign verdict");
        let digest = signed.expr_canonical_digest.clone();
        let safe = name.replace('.', "_");
        std::fs::write(
            verdicts.join(format!("{safe}.json")),
            serde_json::to_vec_pretty(&signed).expect("serialize verdict"),
        )
        .expect("write verdict");
        digest
    };

    let live_digest = sign_and_write(imp_self_theorem("Phase2.live_lemma"), "Phase2.live_lemma");
    let revoked_digest = sign_and_write(
        const_proj_theorem("Phase2.revoked_lemma"),
        "Phase2.revoked_lemma",
    );
    assert_ne!(
        live_digest, revoked_digest,
        "the two fixture theorems must have distinct statement digests"
    );

    // Revoke the second one via a signed revocation list (keyed by its real
    // de Bruijn statement digest).
    let mut list = RevocationList::new("2026-06-25T00:00:00Z".to_string());
    list.revoke(RevocationEntry {
        expr_canonical_digest: revoked_digest.clone(),
        name: "Phase2.revoked_lemma".to_string(),
        revoked_at: "2026-06-25T00:00:00Z".to_string(),
        reason: RevocationReason::NowAxiomDependent,
        detail: "kernel no longer agrees".to_string(),
        clean_commit_at_revocation: "c0ffee".to_string(),
    });
    list.sign_with(&backend).expect("sign revocation list");
    std::fs::write(
        dir.join("revocation-list.json"),
        serde_json::to_vec_pretty(&list).expect("serialize list"),
    )
    .expect("write list");

    (
        "Phase2.live_lemma".to_string(),
        "Phase2.revoked_lemma".to_string(),
        revoked_digest,
    )
}

#[test]
fn test_serve_phase2_verdict_audit_submit() {
    let core = tempfile::tempdir().expect("core tempdir");
    build_fixture_core(core.path());
    let raudit = tempfile::tempdir().expect("reauditor tempdir");
    let (live, revoked, _revoked_digest) = build_reauditor_output(raudit.path());

    let queue = tempfile::tempdir().expect("submit queue tempdir");
    let service = start_service_with(core.path(), None, Some(raudit.path()), Some(queue.path()));
    let port = service.port;

    // -- /verdict/{name} : live KernelVerified ----------------------------
    let v = get(port, &format!("/verdict/{live}"));
    assert_eq!(v.status, 200, "verdict for a re-audited decl is 200");
    let vj = v.json();
    assert_eq!(vj["name"].as_str(), Some(live.as_str()));
    assert_eq!(
        vj["verdict"].as_str(),
        Some("KernelVerified"),
        "the live claim serves a KernelVerified badge"
    );
    assert_eq!(vj["revoked"].as_bool(), Some(false));
    assert_eq!(vj["foundational"].as_bool(), Some(true));
    assert!(
        vj["expr_canonical_digest"]
            .as_str()
            .unwrap_or("")
            .starts_with("blake3:"),
        "the de Bruijn digest (the re-verifiable truth) is surfaced"
    );
    assert_eq!(vj["verifier"]["tcb_axioms"].as_u64(), Some(3));
    assert_eq!(vj["signature"]["sig_alg"].as_str(), Some("ed25519"));
    assert!(
        !vj["signature"]["value"].as_str().unwrap_or("").is_empty(),
        "the signature value is present for offline verification"
    );
    // The verbatim signed record is included so a consumer can recompute the
    // canonical bytes and verify offline.
    assert_eq!(
        vj["signed_record"]["schema"].as_str(),
        Some("mathverse-signed-verdict-v1")
    );
    // Honesty contract: the payload states provenance != correctness.
    assert!(
        vj["trust_note"]
            .as_str()
            .unwrap_or("")
            .contains("attests PROVENANCE"),
        "verdict payload carries the provenance honesty note"
    );

    // -- /verdict/{name} : revoked claim → badge stripped -----------------
    let rv = get(port, &format!("/verdict/{revoked}")).json();
    assert_eq!(
        rv["verdict"].as_str(),
        Some("Revoked"),
        "a revoked claim's badge is Revoked even though its signed kind was KernelVerified"
    );
    assert_eq!(rv["revoked"].as_bool(), Some(true));

    // -- /verdict/{name} : not re-audited → 404 (but distinct reason) -----
    let miss = get(port, "/verdict/Phase2.does_not_exist");
    assert_eq!(miss.status, 404, "an un-re-audited decl is 404");
    assert!(
        miss.json()["error"]
            .as_str()
            .unwrap_or("")
            .contains("not re-audited"),
        "the 404 says the decl was not re-audited (verdict dir IS loaded)"
    );

    // -- /audit : summary --------------------------------------------------
    let audit = get(port, "/audit");
    assert_eq!(audit.status, 200, "audit status");
    let aj = audit.json();
    assert_eq!(aj["reaudited"].as_bool(), Some(true));
    assert_eq!(aj["examined"].as_u64(), Some(2), "two signed verdicts");
    assert_eq!(
        aj["signed_kernel_verified"].as_u64(),
        Some(1),
        "only the non-revoked KernelVerified is live"
    );
    assert_eq!(aj["revoked"].as_u64(), Some(1));
    assert_eq!(aj["revocation_list"]["entries"].as_u64(), Some(1));

    // -- POST /submit : Phase-2.1 LIVE staging (not a 501 stub) -----------
    // The front-end holds NO signing key: it validates well-formedness and
    // stages the candidate to the queue with status=pending. It never mints.
    let body = serde_json::to_vec(&Submission {
        declaration: imp_self_theorem("Submit.imp_self_live"),
        note: "submitted via the live front-end".to_string(),
    })
    .expect("serialize submission");
    let submit = post_body(port, "/submit", &body);
    assert_eq!(
        submit.status, 202,
        "a well-formed submission is staged (202)"
    );
    let sj = submit.json();
    assert_eq!(
        sj["status"].as_str(),
        Some("pending"),
        "the front-end stages pending — it never mints"
    );
    let sub_id = sj["submission_id"]
        .as_str()
        .expect("a staged submission carries a submission_id")
        .to_string();
    assert!(
        sub_id.starts_with("sub_"),
        "content-addressed submission id"
    );
    assert!(
        sj["note"].as_str().unwrap_or("").contains("never mints"),
        "the response restates that the front-end holds no key"
    );

    // -- GET /submit/{id} : status lookup (still pending — no publisher yet)
    let status = get(port, &format!("/submit/{sub_id}"));
    assert_eq!(status.status, 200, "submission status lookup is 200");
    let stj = status.json();
    assert_eq!(stj["submission_id"].as_str(), Some(sub_id.as_str()));
    assert_eq!(
        stj["status"].as_str(),
        Some("pending"),
        "no privileged publisher has run, so the candidate is still pending"
    );
    assert!(
        stj["verdict"].is_null(),
        "no signed verdict yet — the front-end never produces one"
    );

    // -- POST /submit : a malformed body is rejected at the door (400) ----
    let bad = post_body(port, "/submit", b"not a submission at all");
    assert_eq!(
        bad.status, 400,
        "a malformed candidate is rejected, never staged"
    );

    // -- GET /submit/{unknown} : honest 404 -------------------------------
    let miss_sub = get(port, "/submit/sub_deadbeef");
    assert_eq!(miss_sub.status, 404, "unknown submission id is 404");

    drop(service);
}

#[test]
fn test_serve_phase2_verdict_unloaded_reports_not_loaded() {
    // No $MATHVERSE_VERDICTS_DIR: /verdict and /audit honestly report that the
    // service serves stored provenance and there is no re-audit data loaded.
    let core = tempfile::tempdir().expect("core tempdir");
    build_fixture_core(core.path());
    let service = start_service_with(core.path(), None, None, None);
    let port = service.port;

    let audit = get(port, "/audit");
    assert_eq!(audit.status, 200, "audit responds even with no verdicts");
    assert_eq!(
        audit.json()["reaudited"].as_bool(),
        Some(false),
        "with no verdict dir, /audit reports reaudited=false"
    );

    let miss = get(port, "/verdict/Anything");
    assert_eq!(miss.status, 404);
    assert!(
        miss.json()["error"]
            .as_str()
            .unwrap_or("")
            .contains("not loaded"),
        "the 404 says re-audit data is not loaded (no verdict dir configured)"
    );

    drop(service);
}

/// Build a Core fixture whose declarations cross-reference each other, so the
/// dependency adjacency (and its inverse) is non-trivial:
///
/// - `Core.base`  — a `Sort`, depended on by nobody itself.
/// - `Core.user_a` — type `Pi(Core.base, Core.base)` ⇒ depends on `Core.base`.
/// - `Core.user_b` — value `App(Core.base, Core.base)` ⇒ depends on `Core.base`.
/// - `Core.hub`    — value `Core.user_a` ⇒ depends on `Core.user_a`.
///
/// Reverse-deps of `Core.base` are `{user_a, user_b}`, and `user_a` (used by
/// `hub`) outranks `user_b` (used by nobody).
fn build_fixture_core_with_deps(dir: &Path) {
    let loader = LibraryLoader::new(dir.to_path_buf());
    loader.init().expect("init core dir");

    let mut writer = ShardWriter::new();
    let base_name = writer.add_string("Core.base");
    let a_name = writer.add_string("Core.user_a");
    let b_name = writer.add_string("Core.user_b");
    let hub_name = writer.add_string("Core.hub");

    let l0 = writer.add_level(FlatLevel::zero());
    let e_sort = writer.add_expr(FlatExpr::sort(l0));
    let e_base = writer.add_expr(FlatExpr::const_ref(base_name, u32::MAX));
    let e_base2 = writer.add_expr(FlatExpr::const_ref(base_name, u32::MAX));
    let e_pi = writer.add_expr(FlatExpr::pi(0, e_base, e_base2));
    let e_app = writer.add_expr(FlatExpr::app(e_base, e_base2));
    let e_a = writer.add_expr(FlatExpr::const_ref(a_name, u32::MAX));

    let mk = |writer: &mut ShardWriter, name_idx, type_idx, value_idx| {
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    };
    use clean_mathverse::types::NO_VALUE;
    mk(&mut writer, base_name, e_sort, NO_VALUE);
    mk(&mut writer, a_name, e_pi, NO_VALUE);
    mk(&mut writer, b_name, e_sort, e_app);
    mk(&mut writer, hub_name, e_sort, e_a);

    loader
        .write_shard(&writer, "dep_core", false)
        .expect("write dep fixture shard");
}

#[test]
fn test_serve_rdeps_finds_ranked_users() {
    let tmp = tempfile::tempdir().expect("tempdir");
    build_fixture_core_with_deps(tmp.path());
    let service = start_service(tmp.path(), None);
    let port = service.port;

    // -- /rdeps/Core.base : direct users, impact-ranked --------------------
    let resp = get(port, "/rdeps/Core.base");
    assert_eq!(resp.status, 200, "rdeps status");
    let body = resp.json();
    assert_eq!(body["root"].as_str(), Some("Core.base"));
    assert_eq!(
        body["count"].as_u64(),
        Some(2),
        "Core.base is used by user_a and user_b"
    );
    assert_eq!(
        body["direct_user_count"].as_u64(),
        Some(2),
        "in-degree of Core.base is 2"
    );
    let deps = body["dependents"].as_array().expect("dependents array");
    // Impact ranking: user_a (used by hub, in-degree 1) before user_b (0).
    assert_eq!(deps[0]["name"].as_str(), Some("Core.user_a"));
    assert_eq!(deps[0]["used_by_count"].as_u64(), Some(1));
    assert_eq!(deps[1]["name"].as_str(), Some("Core.user_b"));
    assert_eq!(deps[1]["used_by_count"].as_u64(), Some(0));

    // -- /uses/{name} alias resolves to the same handler ------------------
    let alias = get(port, "/uses/Core.base");
    assert_eq!(alias.status, 200, "uses alias status");
    assert_eq!(alias.json()["count"].as_u64(), Some(2));

    // -- a leaf (used by nobody) honestly reports zero --------------------
    let leaf = get(port, "/rdeps/Core.hub");
    assert_eq!(leaf.status, 200);
    assert_eq!(
        leaf.json()["count"].as_u64(),
        Some(0),
        "Core.hub is used by nothing"
    );

    // -- unknown declaration : 404 ----------------------------------------
    let miss = get(port, "/rdeps/Core.nope");
    assert_eq!(miss.status, 404, "unknown name is 404");

    drop(service);
}

#[test]
fn test_serve_type_and_equivalent_search() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // The 3 fixture decls all carry the same type (`Sort 0`), so type-directed
    // search by any one of them surfaces the other two; the anchor is excluded.
    build_fixture_core(tmp.path());
    let service = start_service(tmp.path(), None);
    let port = service.port;

    // -- /type?like= : discrimination-tree type search --------------------
    let resp = get(port, "/type?like=Test.kernel_thm");
    assert_eq!(resp.status, 200, "type search status");
    let body = resp.json();
    assert_eq!(body["anchor"].as_str(), Some("Test.kernel_thm"));
    assert_eq!(
        body["count"].as_u64(),
        Some(2),
        "the two type-peers (anchor excluded) must be found"
    );
    let names: Vec<&str> = body["results"]
        .as_array()
        .expect("results array")
        .iter()
        .filter_map(|r| r["name"].as_str())
        .collect();
    assert!(
        names.contains(&"Test.kernel_def") && names.contains(&"Test.choice_user"),
        "type search must surface both same-typed peers, got {names:?}"
    );
    assert!(
        !names.contains(&"Test.kernel_thm"),
        "the anchor itself must be excluded"
    );

    // Missing `like` is a 400; an unknown reference declaration is a 404.
    assert_eq!(get(port, "/type").status, 400, "missing like is 400");
    assert_eq!(
        get(port, "/type?like=Does.Not.Exist").status,
        404,
        "unknown reference declaration is 404"
    );

    // -- /equivalent/{name} : structural-equivalence lookup ---------------
    let eq = get(port, "/equivalent/Test.kernel_thm");
    assert_eq!(eq.status, 200, "equivalent status");
    let eqb = eq.json();
    assert_eq!(eqb["anchor"].as_str(), Some("Test.kernel_thm"));
    assert!(
        eqb["rewrite_canonical_digest"]
            .as_str()
            .is_some_and(|d| d.starts_with("blake3:")),
        "a reconstructable type must yield a rewrite-canonical digest"
    );
    // The fixture ships no baseline.mvix, so the microsecond corpus-wide
    // representative lookup is honestly reported as unavailable.
    assert_eq!(eqb["index_available"].as_bool(), Some(false));
    assert_eq!(eqb["already_in_corpus"].as_bool(), Some(false));
    assert!(eqb["representative"].is_null());

    let miss = get(port, "/equivalent/Does.Not.Exist");
    assert_eq!(miss.status, 404, "unknown declaration is 404");

    drop(service);
}
