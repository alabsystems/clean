// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! With a Mathverse corpus installed, every proof-state answer that reports
//! Mathverse candidates scans the corpus for them, and the scan belongs on the
//! work pool, under the request's deadline, never on a runtime worker (R36 and
//! R87 in `docs/DECISIONS.md`). The scan asserts that
//! in debug builds (`proof_state::mathverse_candidates_for_goal`), so a request
//! path that scans on the runtime panics the test that takes it.
//!
//! A process of its own: the corpus is process-global, and the first install
//! wins (`mathverse_provider::install_global`), so it must be installed before
//! any `ServerState` is built, and the unit tests run without one.

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{Declaration, Environment, Expr, Name};
use clean_mathverse::shard::ShardWriter;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
};
use clean_server::handlers::{
    handle_apply_tactic, handle_get_proof_state, handle_open_obligation, ServerState,
};
use clean_server::mathverse_provider::{install_global, MathverseProvider};
use clean_server::proof_state::{OPEN_OBLIGATION_SCHEMA_VERSION, PROOF_STATE_SCHEMA_VERSION};
use clean_server::{RequestId, Response};
use serde_json::{json, Value};
use std::sync::OnceLock;

/// A wait for something that must happen, as every request's timeout here.
const HANG_MS: u64 = 60_000;

/// The corpus's one constant, `corpus_lemma : Prop`, stamped kernel-verified
/// with no axioms so it passes the trust gate.
const LEMMA: &str = "corpus_lemma";

/// Install a one-constant corpus as the process's provider, once.
fn corpus_installed() {
    static CORPUS: OnceLock<tempfile::TempDir> = OnceLock::new();
    CORPUS.get_or_init(|| {
        let dir = tempfile::tempdir().expect("a scratch directory");
        let mut writer = ShardWriter::new();
        let name_idx = writer.add_string(LEMMA);
        let level = writer.add_level(FlatLevel::zero());
        let prop = writer.add_expr(FlatExpr::sort(level));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: prop,
            value_idx: prop,
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
        writer
            .write_to_file(dir.path().join("corpus.mathverse"))
            .expect("write the corpus shard");
        let provider = MathverseProvider::from_dir(dir.path());
        assert!(
            provider.is_loaded(),
            "the corpus loads: this test's premise"
        );
        install_global(provider);
        dir
    });
}

/// A server whose environment states the corpus lemma and has a proof of it.
fn server() -> ServerState {
    corpus_installed();
    let mut env = Environment::with_prelude();
    for (name, type_) in [
        (LEMMA, Expr::prop()),
        (
            "corpus_lemma_proof",
            Expr::const_(Name::from_string(LEMMA), vec![]),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .expect("the kernel checks the corpus lemma's declarations");
    }
    ServerState::new().with_env(env)
}

fn answer(what: &str, response: Response) -> Value {
    assert!(response.error.is_none(), "{what}: {:?}", response.error);
    response.result.expect("a result")
}

fn names(candidates: &Value) -> Vec<String> {
    candidates
        .as_array()
        .map(|candidates| {
            candidates
                .iter()
                .filter_map(|candidate| candidate["name"].as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default()
}

/// An obligation that admits one live state, and a tactic that solves it:
/// the solved state is refused at the lifecycle limit, and the refusal reports
/// the Mathverse candidates of the state the tactic ran on. Until R36's
/// follow-up that scan ran on the runtime, after the tactic's work had
/// answered (its slot went to the tactic). The other proof-state answers that
/// scan run here too, so any of them that scanned on the runtime fails this.
#[tokio::test]
async fn proof_state_answers_scan_the_corpus_off_the_runtime() {
    let state = server();
    let goal = Expr::const_(Name::from_string(LEMMA), vec![]);
    let opened = answer(
        "openObligation",
        handle_open_obligation(
            &state,
            RequestId::Number(1),
            serde_json::from_value(json!({
                "schema_version": OPEN_OBLIGATION_SCHEMA_VERSION,
                "environment_id": "corpus-scans",
                "domain_profile": "general",
                "goal": {
                    "pretty": LEMMA,
                    "expr": serde_json::to_value(&goal).expect("the goal's JSON"),
                },
                "trust_policy": "constructive-only",
                "ttl_sec": 600,
                "max_states": 1,
                "min_schema_version": PROOF_STATE_SCHEMA_VERSION,
                "max_schema_version": PROOF_STATE_SCHEMA_VERSION,
                "timeout_ms": HANG_MS,
            }))
            .expect("openObligation params"),
        )
        .await,
    );
    let state_id = opened["state_id"].clone();
    let goal_id = opened["initial_snapshot"]["goals"][0]["goal_id"].clone();
    let apply = |tactic: &str| {
        serde_json::from_value(json!({
            "state_id": state_id,
            "goal_id": goal_id,
            "tactic": tactic,
            "timeout_ms": HANG_MS,
        }))
        .expect("applyTactic params")
    };

    let refused = answer(
        "the refused applyTactic",
        handle_apply_tactic(
            &state,
            RequestId::Number(2),
            apply("exact corpus_lemma_proof"),
        )
        .await,
    );
    assert_eq!(refused["success"], json!(false), "{refused}");
    assert_eq!(
        refused["error"]["code"],
        json!("LIFECYCLE_LIMIT_EXCEEDED"),
        "{refused}"
    );
    assert!(
        names(&refused["mathverse_candidates"]).contains(&LEMMA.to_string()),
        "the refusal reports the candidates of the state the tactic ran on: {refused}"
    );

    let failed = answer(
        "the failed applyTactic",
        handle_apply_tactic(&state, RequestId::Number(3), apply("exact no_such_proof")).await,
    );
    assert_eq!(failed["success"], json!(false), "{failed}");
    for format in ["full", "compact", "llm"] {
        answer(
            "getProofState",
            handle_get_proof_state(
                &state,
                RequestId::Number(4),
                serde_json::from_value(json!({
                    "state_id": state_id,
                    "format": format,
                    "timeout_ms": HANG_MS,
                }))
                .expect("getProofState params"),
            )
            .await,
        );
    }
}
