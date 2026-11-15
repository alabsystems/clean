// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Work that outlived its request, or ran on the runtime's threads (R36 in
//! `docs/DECISIONS.md`), each test pinned by a defect R34 and its reviews left
//! open:
//!
//! * `importModule`'s load did not stop at its deadline: past it, the load
//!   read, decoded and registered every module, holding its work slot.
//! * The environment a writer replaced was freed on a runtime worker, which
//!   served nothing else until the free ended.
//! * The certificate codec methods, `saveEnvironment`, `getEnvironment` with
//!   its JSON and the proof-state searches decoded, encoded or searched on
//!   the runtime's threads with no timeout.
//!
//! Every wait for something that must happen is a one-minute hang detector,
//! never a latency budget.

use super::concurrent_writers::bare_state_with;
use super::external_cert::create_sample_certs;
use super::free_gate::gated_source;
use crate::dispatch::dispatch_request;
use crate::handlers::work::WorkPool;
use crate::handlers::*;
use crate::rpc::Response;
use clean_kernel::cert::ProofCert;
use clean_kernel::{Environment, Level};
use serde_json::{json, Value};
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

/// A wait for something that must happen.
const HANG: Duration = Duration::from_secs(60);

/// `RpcError::timeout`'s code.
const TIMEOUT: i32 = -32004;

/// Send `method` through the dispatcher; it must answer within the hang
/// detector.
async fn sent(state: &ServerState, method: &str, params: Value) -> Response {
    tokio::time::timeout(
        HANG,
        dispatch_request(method, Some(params), RequestId::Number(1), state, None),
    )
    .await
    .unwrap_or_else(|_| panic!("{method} was not answered within the hang detector"))
}

/// Send `method` and return its result; it must succeed.
async fn result_of(state: &ServerState, method: &str, params: Value) -> Value {
    let response = sent(state, method, params).await;
    assert!(response.error.is_none(), "{method}: {:?}", response.error);
    response.result.expect("a result")
}

/// `.olean` bytes of an empty module importing `imports`.
fn module_importing(imports: &[(&str, bool)]) -> Vec<u8> {
    clean_olean::OleanExporter::export_with_env(
        &Environment::default(),
        imports,
        &[],
        "c0de000000000000000000000000000000000003",
    )
    .expect("export the fixture module")
}

/// `importModule`'s load read, decoded and registered every module after its
/// request had answered the timeout error, holding its work slot. It reads
/// the deadline before each module now. Here the root imports a named pipe
/// that imports another: the load waits on the first until the test writes
/// it, after the import has answered; past its deadline it stops there and
/// gives its slot back. The old load opened the second pipe, which nobody
/// writes, and kept its slot (to the hang detector). Nothing is imported and
/// nothing enters the module cache.
#[cfg(unix)]
#[tokio::test]
async fn import_module_stops_its_load_at_its_deadline() {
    use super::concurrent_writers::{answered, named_pipe, pipe_writer, spawned, wait_until_idle};

    let dir = tempfile::tempdir().expect("a scratch directory");
    std::fs::write(
        dir.path().join("CutRoot.olean"),
        module_importing(&[("CutFirst", false)]),
    )
    .expect("write the root module");
    let first = dir.path().join("CutFirst.olean");
    named_pipe(&first);
    named_pipe(&dir.path().join("CutSecond.olean"));
    let state = bare_state_with(WorkPool::new(2));
    let before = state.env.revision().await;

    let s = Arc::clone(&state);
    let params: ImportModuleParams = serde_json::from_value(json!({
        "module": "CutRoot",
        "search_paths": [dir.path().to_string_lossy()],
        "timeout_ms": 300,
        "token": super::launch_token_of(&state),
    }))
    .expect("importModule params");
    let importing =
        spawned(async move { handle_import_module(&s, RequestId::Number(1), params).await });
    let mut pipe = pipe_writer(first).await;
    let (response, _) = answered("the import", importing).await;
    assert_eq!(response.error.map(|e| e.code), Some(TIMEOUT));

    let bytes = module_importing(&[("CutSecond", false)]);
    tokio::task::spawn_blocking(move || {
        use std::io::Write;
        pipe.write_all(&bytes)
            .expect("write the first module down its pipe");
    })
    .await
    .expect("the writing thread");
    wait_until_idle(&state).await;
    assert_eq!(state.env.revision().await, before, "a cut load published");
    assert!(
        state.olean_cache.is_empty(),
        "a load cut before any decode filled the module cache"
    );
}

/// `loadEnvironment` in replace mode freed the environment it replaced on the
/// runtime. The old environment here holds a gated source (`free_gate.rs`),
/// so its free lasts until the test releases it; on this one-thread runtime,
/// a free on the runtime's thread can never be released, and the answer
/// waited for it to the hang detector. Now the free runs off the runtime: a
/// `check` is answered while it runs, and then the test releases it.
#[tokio::test]
async fn load_environment_replace_frees_the_old_environment_off_the_runtime() {
    let (source, gate) = gated_source();
    let mut env = Environment::new();
    env.set_constant_source(source);
    let state = super::temp_rooted_state().with_env(env);
    let dir = tempfile::tempdir().expect("a scratch directory");
    let path = dir.path().join("replacement.bincode");
    Environment::new()
        .save_to_file(&path)
        .expect("save the replacement");

    let replaced = result_of(
        &state,
        "loadEnvironment",
        json!({
            "path": path.to_string_lossy(),
            "replace": true,
            "replace_unchecked": true,
            "token": super::launch_token_of(&state),
            "timeout_ms": HANG.as_millis() as u64,
        }),
    )
    .await;
    assert_eq!(replaced["success"], json!(true), "{replaced}");
    let runtime = std::thread::current().id();
    gate.freeing().await;
    let check = result_of(
        &state,
        "check",
        json!({ "code": "Type", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    assert_eq!(check["valid"], json!(true), "{check}");
    let freed = gate.release().await;
    assert!(
        freed.released,
        "the old environment was freed on the runtime's thread: the test could not release it"
    );
    assert_ne!(freed.on, runtime);
}

/// The requests whose work decodes, encodes or searches without a bound of
/// its own, with parameters that succeed, made with the pool free.
async fn unbounded_requests(state: &ServerState, dir: &Path) -> Vec<(&'static str, Value)> {
    let cert = serde_json::to_value(ProofCert::Sort {
        level: Level::zero(),
    })
    .expect("a certificate's JSON");
    let compressed = result_of(state, "compressCert", json!({ "cert": cert })).await;
    let archived = result_of(state, "archiveCert", json!({ "cert": cert })).await;
    let samples = serde_json::to_value(create_sample_certs(10)).expect("the samples' JSON");
    let trained = result_of(state, "trainDict", json!({ "samples": samples })).await;
    let dictionary = trained["dictionary"].clone();
    let dict_archived = result_of(
        state,
        "archiveCertWithDict",
        json!({ "cert": cert, "dictionary": dictionary }),
    )
    .await;
    let opened = result_of(
        state,
        "initProofState",
        json!({ "theorem": "True", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    let search = json!({ "state_id": opened["state_id"], "goal_id": "g0" });
    vec![
        ("compressCert", json!({ "cert": cert })),
        (
            "decompressCert",
            json!({ "compressed": compressed["compressed"] }),
        ),
        ("archiveCert", json!({ "cert": cert })),
        ("unarchiveCert", json!({ "archive": archived["archive"] })),
        ("trainDict", json!({ "samples": samples })),
        (
            "archiveCertWithDict",
            json!({ "cert": cert, "dictionary": dictionary }),
        ),
        (
            "unarchiveCertWithDict",
            json!({ "archive": dict_archived["archive"], "dictionary": dictionary }),
        ),
        (
            "saveEnvironment",
            json!({ "path": dir.join("saved.bincode").to_string_lossy() }),
        ),
        ("getEnvironment", json!({ "include_json": true })),
        ("proofState.searchTheorems", search.clone()),
        ("proofState.searchTactics", search),
    ]
}

/// The certificate codec methods, `saveEnvironment`, `getEnvironment` with
/// its JSON and the proof-state searches ran on the runtime's threads with no
/// timeout: a large input or environment held a runtime worker for as long as
/// the work took. Their work runs on the pool now, under a `timeout_ms`.
/// Here the pool's only slot is held: each waits for it inside its timeout
/// and answers the timeout error. Requests whose work is bounded take no slot
/// and are answered meanwhile. With the slot free, each answers again.
#[tokio::test]
async fn unbounded_methods_wait_for_a_work_slot_inside_their_timeout() {
    let mut state = super::temp_rooted_state().with_env(Environment::with_prelude());
    state.work = WorkPool::new(1);
    let dir = tempfile::tempdir().expect("a scratch directory");
    let requests = unbounded_requests(&state, dir.path()).await;
    let opened = result_of(
        &state,
        "initProofState",
        json!({ "theorem": "True", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;

    let slot = state.work.slot().await.expect("the pool's one slot");
    let mut unbounded = Vec::new();
    for (method, params) in &requests {
        let mut params = params.clone();
        params["timeout_ms"] = json!(300);
        let response = sent(&state, method, params).await;
        if response.error.as_ref().map(|e| e.code) != Some(TIMEOUT) {
            unbounded.push(*method);
        }
    }
    assert!(
        unbounded.is_empty(),
        "answered without a work slot: {unbounded:?}"
    );
    for (method, params) in [
        ("getEnvironment", json!({ "timeout_ms": 300 })),
        ("serverInfo", json!({})),
        (
            "getProofState",
            json!({ "state_id": opened["state_id"], "format": "compact", "timeout_ms": 300 }),
        ),
    ] {
        result_of(&state, method, params).await;
    }
    drop(slot);

    for (method, params) in requests {
        result_of(&state, method, params).await;
    }
}

/// A constant source that serves nothing: a handle on an environment, whose
/// strong count says how many environments hold it.
#[derive(Debug)]
struct Counted;

impl clean_kernel::env::ConstantSource for Counted {
    fn get(&self, _name: &clean_kernel::Name) -> Option<&clean_kernel::env::ConstantInfo> {
        None
    }

    fn contains(&self, _name: &clean_kernel::Name) -> bool {
        false
    }
}

/// Every read of a cached proof state copied it, and a proof state holds a
/// whole environment: each proof-state request copied an environment on the
/// thread that read it, under the cache's one lock. A read shares the state
/// now. Here the environment holds a counted source, so each copy of it shows
/// as one more holder.
#[tokio::test]
async fn reading_a_cached_proof_state_copies_no_environment() {
    let source: Arc<dyn clean_kernel::env::ConstantSource> = Arc::new(Counted);
    let mut env = Environment::with_prelude();
    env.set_constant_source(Arc::clone(&source));
    let state = ServerState::new().with_env(env);
    let opened = result_of(
        &state,
        "initProofState",
        json!({ "theorem": "True", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    let id: crate::proof_state::StateId = opened["state_id"]
        .as_str()
        .expect("a state id")
        .parse()
        .expect("a state id");
    let holders = Arc::strong_count(&source);
    let reads: Vec<_> = (0..3)
        .map(|_| state.proof_cache.get(&id).expect("the state is cached"))
        .collect();
    assert_eq!(
        Arc::strong_count(&source),
        holders,
        "each read of the cached state copied its environment"
    );
    drop(reads);
}

/// The proof-state cache freed the states it let go (closed, expired,
/// evicted) on the thread that let them go: `proofState.close` on a runtime
/// worker. Here the only environment left holding a gated source is the
/// cached state's, so closing the state frees it, and the free lasts until the
/// test releases it; a `check` is answered meanwhile.
#[tokio::test]
async fn closing_a_proof_state_frees_its_environment_off_the_runtime() {
    let (source, gate) = gated_source();
    let mut env = Environment::with_prelude();
    env.set_constant_source(source);
    let state = ServerState::new().with_env(env);
    let opened = result_of(
        &state,
        "initProofState",
        json!({ "theorem": "True", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    // The shared environment lets its share go: the cached state's is the
    // last.
    state.env.replace(Environment::with_prelude()).await;
    let closed = result_of(
        &state,
        "proofState.close",
        json!({ "state_id": opened["state_id"] }),
    )
    .await;
    assert_eq!(closed["closed"], json!(true), "{closed}");
    let runtime = std::thread::current().id();
    gate.freeing().await;
    let check = result_of(
        &state,
        "check",
        json!({ "code": "Type", "timeout_ms": HANG.as_millis() as u64 }),
    )
    .await;
    assert_eq!(check["valid"], json!(true), "{check}");
    let freed = gate.release().await;
    assert!(
        freed.released,
        "the closed state's environment was freed on the runtime's thread"
    );
    assert_ne!(freed.on, runtime);
}
