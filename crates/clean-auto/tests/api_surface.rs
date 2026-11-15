// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "support/rustc.rs"]
mod rustc_support;

#[path = "support/metadata.rs"]
mod metadata_support;

use clean_auto::oracle::{sort_oracle_candidates, OracleCandidate, OracleRequest};
use clean_auto::premise::{HybridSelector, MePoSelector, PremiseDatabase, PremiseId};
use clean_auto::{SmtBridge, SmtVerificationResult};
use clean_kernel::{Environment, Expr, Name};
use serial_test::file_serial;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_compile_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "clean_auto_api_surface_{test_name}_{}_{}",
        std::process::id(),
        nanos
    ))
}

fn compile_external_snippet(test_name: &str, source: &str) -> std::process::Output {
    let metadata = metadata_support::clean_auto();
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    // TRUST OPT-OUT — use Cargo's selected `RUSTC` so this snippet and the
    // linked crate metadata always share a compiler ABI. When that compiler is
    // Trust, disable obligation checking for this throwaway API-surface probe;
    // the snippet proves only that a public name is reachable.
    // The compiler is Trust (owner directive 2026-09-28); there is no retry
    // without the opt-out.
    let run_rustc = || {
        let mut cmd = Command::new(rustc_support::cargo_rustc());
        cmd.arg("-Ztrust-verify=off");
        cmd.arg("--crate-type")
            .arg("lib")
            .arg("--edition")
            .arg("2021")
            .arg("--emit")
            .arg("metadata")
            .arg("--out-dir")
            .arg(&compile_dir)
            .arg(&source_path)
            .arg("--extern")
            .arg(format!("clean_auto={}", metadata.artifact.display()));
        metadata.configure(&mut cmd);
        cmd.output()
    };
    let output = run_rustc().expect("trustc should be runnable from integration tests");

    let _ = fs::remove_dir_all(&compile_dir);
    output
}

fn assert_external_compile_fails(test_name: &str, source: &str, expected_fragments: &[&str]) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "snippet unexpectedly compiled successfully\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    for fragment in expected_fragments {
        assert!(
            stderr.contains(fragment),
            "expected rustc stderr to contain `{fragment}`\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

fn assert_external_compile_succeeds(test_name: &str, source: &str) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "snippet failed to compile\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn test_root_reexports_focus_on_primary_smt_entry_points() {
    let env = Environment::new();
    let _bridge = SmtBridge::new(&env);
    let _verification: Option<SmtVerificationResult> = None;

    // Since #2386, SMT-internal types (TermId, SmtTerm, SmtInt,
    // TheoryLiteral, TheorySolver, etc.) are pub(crate) — external
    // consumers use SmtBridge directly.

    let mut premise_db = PremiseDatabase::new();
    let premise_id: PremiseId = premise_db.add(Name::from_string("Eq"), Expr::prop());
    assert_eq!(premise_db.len(), 1);
    assert!(premise_db.get(premise_id).is_some());

    let mepo = MePoSelector::new(&premise_db).with_max_premises(4);
    let hybrid = HybridSelector::new(&premise_db).with_max_premises(4);
    assert!(mepo.select(&Expr::prop()).is_empty());
    assert!(hybrid.select(&Expr::prop()).is_empty());

    let request = OracleRequest::new("True").with_hypothesis("h", "True");
    assert!(request.format_prompt().contains("theorem goal"));

    let mut candidates = [
        OracleCandidate::new("exact h", 0.25),
        OracleCandidate::new("trivial", 0.75),
    ];
    sort_oracle_candidates(&mut candidates);
    assert_eq!(candidates[0].tactic_text, "trivial");
}

#[test]
#[file_serial]
fn test_internal_smt_types_are_not_nameable_from_crate_root() {
    assert_external_compile_fails(
        "hidden_smt_types",
        r#"
#![allow(unused_imports)]
use clean_auto::{SmtStats, TermId};
"#,
        &["SmtStats", "TermId"],
    );
}

#[test]
#[file_serial]
fn test_smt_bridge_stats_stays_crate_private() {
    assert_external_compile_fails(
        "private_bridge_stats",
        r#"
use clean_auto::SmtBridge;

fn touch<'env>(bridge: &SmtBridge<'env>) {
    let _ = bridge.stats();
}
"#,
        &["stats", "private"],
    );
}

#[test]
#[file_serial]
fn test_smt_bridge_proof_trail_stays_crate_private() {
    assert_external_compile_fails(
        "private_bridge_trail",
        r#"
use clean_auto::SmtBridge;

fn touch<'env>(bridge: &SmtBridge<'env>) {
    let _ = bridge.proof_trail();
}
"#,
        &["proof_trail", "private"],
    );
}

#[test]
#[file_serial]
fn test_proof_profile_policy_fields_stay_private() {
    assert_external_compile_fails(
        "private_proof_profile_fields",
        r#"
use clean_auto::bridge::ay_contract::ProofProfile;

fn touch(profile: &ProofProfile) {
    let _ = &profile.format;
    let _ = profile.verification_tier;
    let _ = &profile.accepted_theories;
}
"#,
        &[
            "format",
            "verification_tier",
            "accepted_theories",
            "private",
        ],
    );
}

#[test]
#[file_serial]
fn test_budgeted_kernel_reconstruction_api_is_nameable() {
    assert_external_compile_succeeds(
        "budgeted_kernel_reconstruction",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::ay_contract::{TrustBudget, VariableMapping, AyLogic, AyProofBackend};

fn touch() {
    let _budget = TrustBudget::AtMost(1);
    let _strict = TrustBudget::ZeroTrust;
    let _logic = AyLogic::QfUf;
    let _map = VariableMapping::new();
    let _method = AyProofBackend::attempt_kernel_reconstruction_with_budget;
}
"#,
    );
}

/// What Trust names from outside the crate once its Clean pin carries the
/// effort entry: the entry itself (its certify lanes move onto it), and an
/// undecided answer built and read with its reason, which is the edit its two
/// trust-certify tests that build `Unknown` make (docs/DECISIONS.md,
/// R-AY-PROOF-EFFORT-20261011).
#[test]
#[file_serial]
fn test_effort_entry_and_unknown_reason_are_nameable() {
    assert_external_compile_succeeds(
        "effort_entry_and_unknown_reason",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::ay_contract::{AyProofBackend, AyProofResult, AyUnknownReason};
use std::num::NonZeroU64;
use std::time::Duration;

fn count_spent(backend: &mut AyProofBackend) -> bool {
    matches!(
        backend.check_sat_with_effort(NonZeroU64::MIN, Duration::from_secs(1)),
        Ok(AyProofResult::Unknown { reason: AyUnknownReason::ResourceLimit, .. })
    )
}

fn undecided() -> AyProofResult {
    AyProofResult::Unknown { reason: AyUnknownReason::Unknown, detail: None }
}
"#,
    );
}

/// Trust's clean-origin gate turns the counted induction entry into a compile
/// decision at its next Clean pin (docs/DECISIONS.md,
/// R-INDUCTION-BACKSTOP-20261014). It names the entry from outside the crate
/// and matches every answer with no wildcard: `InductionSearch` is
/// deliberately exhaustive, so a new answer is a compile error there, never a
/// silent default.
#[test]
#[file_serial]
fn test_counted_induction_entry_is_matched_exhaustively_from_outside() {
    assert_external_compile_succeeds(
        "counted_induction_entry",
        r#"
#![allow(dead_code)]
use clean_auto::{AutomationEngine, InductionSearch};

fn gate(answer: InductionSearch) -> Result<bool, &'static str> {
    match answer {
        InductionSearch::Proved(proof) => Ok(proof.proof_context().is_none()),
        InductionSearch::NotProved => Ok(false),
        InductionSearch::CountLimit(limit) => Err(limit),
        InductionSearch::BackstopFired => Err("could not run: the backstop fired"),
    }
}

fn entry() {
    let _counted = AutomationEngine::prove_by_induction_counted;
}
"#,
    );
}

/// Downstream exhaustive matches on `#[non_exhaustive]` enums (through the
/// curated contract) must include a wildcard arm. Part of #2735, #2774.
#[test]
#[file_serial]
fn test_non_exhaustive_enums_reject_exhaustive_downstream_match() {
    assert_external_compile_fails(
        "non_exhaustive_no_wildcard",
        r#"
use clean_auto::bridge::ay_contract::AyProofResult;

fn touch(r: AyProofResult) -> bool {
    match r {
        AyProofResult::Sat => true,
        AyProofResult::Unsat { .. } => false,
        AyProofResult::Unknown { .. } => false,
    }
}
"#,
        &["non-exhaustive"],
    );
}

/// Downstream matches with a wildcard arm still compile through the curated
/// `ay_contract` path after `#[non_exhaustive]` (Part of #2735, #2774).
#[test]
#[file_serial]
fn test_non_exhaustive_enums_accept_wildcard_downstream_match() {
    assert_external_compile_succeeds(
        "non_exhaustive_wildcard",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::ay_contract::{
    AyLogic, TrustBudget, ReconstructionQuality,
    ResidualTrustSource, AyProofResult,
};

fn logic(l: AyLogic) -> &'static str {
    match l {
        AyLogic::QfLia => "lia",
        _ => "other",
    }
}

fn budget(b: TrustBudget) -> &'static str {
    match b {
        TrustBudget::Unlimited => "any",
        _ => "restricted",
    }
}

fn quality(q: ReconstructionQuality) -> bool {
    match q {
        ReconstructionQuality::FullyVerified => true,
        _ => false,
    }
}

fn source(s: ResidualTrustSource) -> &'static str {
    match s {
        ResidualTrustSource::ArithmeticBoundary => "arith",
        _ => "other",
    }
}

fn proof(p: AyProofResult) -> bool {
    match p {
        AyProofResult::Sat => true,
        _ => false,
    }
}
"#,
    );
}

/// The raw `ay_backend` module path is no longer externally importable after
/// #2774 made it `pub(crate)`. This compile-fail test proves downstream code
/// cannot reach backend-only names through the old path.
#[test]
#[file_serial]
fn test_ay_backend_raw_module_not_externally_importable() {
    assert_external_compile_fails(
        "ay_backend_raw_module_hidden",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::ay_backend::{
    ProofFormat, ProofProfile, SmtlibTriggerPattern, proof_formats,
};
"#,
        &["ay_backend"],
    );
}

/// Curated `ay_contract` names remain downstream-nameable without exposing the
/// full raw backend surface (Part of #2766).
#[test]
#[file_serial]
fn test_ay_contract_curated_surface_is_nameable() {
    assert_external_compile_succeeds(
        "ay_contract_curated_surface",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::ay_contract::{
    verify_alethe_proof, KernelReconstructionCandidate, ProofProfile,
    ReconstructionQuality, ResidualTrustSource, ResidualTrustSummary,
    TriggerPolicy, TrustBudget, VariableMapping, VerifyError, AyBackend,
    AyBackendConfig, AyError, AyLogic, AyProofBackend, AyProofQuality,
    AyProofResult, AyResult, AySolveEnvelope, AySolveResult,
    AySolveVerification, AyTerm, AyUnknownReason, AyVerificationLevel,
    AyVerificationSummary,
};

fn touch_types(
    _candidate: Option<KernelReconstructionCandidate>,
    _backend: Option<AyBackend>,
    _config: Option<AyBackendConfig>,
    _error: Option<AyError>,
    _verify_error: Option<VerifyError>,
    _result: Option<AyResult<()>>,
    _envelope: Option<AySolveEnvelope>,
    _solve_result: Option<AySolveResult>,
    _unknown_reason: Option<AyUnknownReason>,
    _verification: Option<AySolveVerification>,
    _verification_level: Option<AyVerificationLevel>,
    _verification_summary: Option<AyVerificationSummary>,
) {}

fn touch_result(report: &AySolveEnvelope) -> AySolveResult {
    report.solve_result()
}

fn touch_reason(report: &AySolveEnvelope) -> Option<AyUnknownReason> {
    report.unknown_reason()
}

fn touch_term_lane(backend: &mut AyBackend) {
    let x: AyTerm = backend.fresh_bool("x");
    let y: AyTerm = backend.not(x);
    backend.assert_term(y);
}

fn touch_proof_quality(result: AyProofResult) -> Option<bool> {
    match result {
        AyProofResult::Unsat { quality, .. } => quality.map(|q| q.is_complete()),
        _ => None,
    }
}

fn touch_items() {
    let _verify = verify_alethe_proof;
    let _profile = ProofProfile::carcara_verified();
    let _logic = AyLogic::QfUf;
    let _trigger = TriggerPolicy::Auto;
    let _budget = TrustBudget::ZeroTrust;
    let _budget_cap = TrustBudget::AtMost(1);
    let _quality = ReconstructionQuality::FullyVerified;
    let _proof_quality: Option<AyProofQuality> = None;
    let _source = ResidualTrustSource::ArithmeticBoundary;
    // Accessors are the only public read surface for trust envelopes
    // (constructors moved to test-utils lane). Part of #2773.
    let _quality_fn = ReconstructionQuality::trust_count;
    let _proof_quality_fn = AyProofQuality::is_complete;
    let _mapping = VariableMapping::new();
    let _proof = AyProofResult::Sat;
    let _term: Option<AyTerm> = None;
    let _fresh_bool: fn(&mut AyBackend, &str) -> AyTerm = AyBackend::fresh_bool;
    let _assert_term: fn(&mut AyBackend, AyTerm) = AyBackend::assert_term;
    let _backend_ctor = AyBackend::with_config;
    let _config = AyBackendConfig::with_proofs(AyLogic::QfUf)
        .trigger_policy(TriggerPolicy::Auto);
    let _proof_backend_ctor = AyProofBackend::new_with_proofs;
    let _kernel_attempt = AyProofBackend::attempt_kernel_reconstruction_with_budget;
    let _verify_error: Option<VerifyError> = None;
    let _result: Option<AyResult<()>> = None;
    let _solve_envelope: Option<AySolveEnvelope> = None;
    let _solve_result: Option<AySolveResult> = None;
    let _unknown_reason: Option<AyUnknownReason> = None;
    let _solve_verification: Option<AySolveVerification> = None;
    let _solve_verification_level: Option<AyVerificationLevel> = None;
    let _solve_verification_summary: Option<AyVerificationSummary> = None;
    let _touch_result = touch_result;
    let _touch_reason = touch_reason;
    let _touch_term_lane = touch_term_lane;
    let _touch_proof_quality = touch_proof_quality;
    touch_types(
        None,
        None,
        Some(_config),
        None,
        _verify_error,
        _result,
        _solve_envelope,
        _solve_result,
        _unknown_reason,
        _solve_verification,
        _solve_verification_level,
        _solve_verification_summary,
    );
}
"#,
    );
}

/// Kernel-checked computational BitVec identities are part of the curated
/// provider contract when the reconstruction lane is enabled. Keep an actual
/// downstream compile pin here: otherwise these re-exports can become stranded
/// in the crate-private backend again while internal tests continue to pass.
#[cfg(feature = "ay-bv-blast")]
#[test]
#[file_serial]
fn test_ay_contract_bv_compute_identity_surface_is_nameable() {
    assert_external_compile_succeeds(
        "ay_contract_bv_compute_identity_surface",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::ay_contract::{
    reconstruct_bv_compute_identity, BvComputeIdentity, BvComputeReconstruction,
};

fn touch() {
    let _reconstruct = reconstruct_bv_compute_identity;
    let _identity = BvComputeIdentity::SubSelf;
    let _reconstruction: Option<BvComputeReconstruction> = None;
}
"#,
    );
}

#[test]
#[file_serial]
fn test_ay_contract_hides_raw_sort_model_helpers() {
    assert_external_compile_fails(
        "ay_contract_hides_raw_sort_model_helpers",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::ay_contract::AyBackend;

fn touch(backend: &mut AyBackend) {
    let _ = AyBackend::fresh_array;
    let _ = AyBackend::const_array;
    let _ = AyBackend::get_model;
    let _ = AyBackend::register_fvar;
    let _ = backend;
}
"#,
        &["fresh_array", "const_array", "get_model", "register_fvar"],
    );
}

/// Backend-only proof-format and trigger names must stay unavailable from the
/// curated `ay_contract` module (Part of #2766).
#[test]
#[file_serial]
fn test_ay_contract_rejects_backend_only_names() {
    assert_external_compile_fails(
        "ay_contract_backend_only_names",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::ay_contract::{
    ProofFormat, SmtlibTriggerPattern, proof_formats,
};
"#,
        &["ProofFormat", "SmtlibTriggerPattern", "proof_formats"],
    );
}

/// Backend-only helpers that mention hidden proof-format or trigger types must
/// not remain callable through the curated `ay_contract` surface.
#[test]
#[file_serial]
fn test_ay_contract_rejects_backend_only_helpers() {
    assert_external_compile_fails(
        "ay_contract_backend_only_helpers",
        r#"
use clean_auto::bridge::ay_contract::{ProofProfile, AyBackend, AyLogic, AyProofBackend};

fn touch(profile: &ProofProfile, backend: &AyProofBackend, runtime_backend: &mut AyBackend) {
    let _ = profile.format();
    let _ = backend.forall_with_triggers(&[("x", "Int")], "(= x x)", &[]);
    let _ = backend.exists_with_triggers(&[("x", "Int")], "(= x x)", &[]);
    let _ = runtime_backend.forall_with_triggers(&[], unreachable!(), &[]);
    let _ = runtime_backend.exists_with_triggers(&[], unreachable!(), &[]);
    let _ = AyProofBackend::new_with_proofs(AyLogic::QfUf);
}
"#,
        &["format", "forall_with_triggers", "exists_with_triggers"],
    );
}

/// Trust envelope constructors must be absent from the default curated surface.
/// They are only available through the `test-utils` feature gate. Part of #2773.
#[test]
#[file_serial]
fn test_ay_contract_rejects_trust_envelope_constructors() {
    assert_external_compile_fails(
        "ay_contract_trust_envelope_constructors",
        r#"
use clean_auto::bridge::ay_contract::{
    ResidualTrustSource, ResidualTrustSummary,
};

fn try_construct_residual() -> ResidualTrustSummary {
    ResidualTrustSummary::from_source(ResidualTrustSource::ArithmeticBoundary)
}
"#,
        &["from_source"],
    );
}

// --- #2882 API consistency tests below ---

/// `SmtProofResult` must be nameable and its public accessors callable
/// through both the crate root and the `bridge` module path. Part of #2882.
#[test]
#[file_serial]
fn test_smt_proof_result_is_nameable_and_accessible() {
    assert_external_compile_succeeds(
        "smt_proof_result_nameable",
        r#"
#![allow(dead_code)]
use clean_auto::SmtProofResult;
use clean_auto::bridge::SmtProofResult as BridgeSmtProofResult;

fn touch(r: &SmtProofResult) {
    let _term = r.proof_term();
    let _sketch = r.proof_sketch();
    let _method = r.method();
}

fn touch_bridge(r: &BridgeSmtProofResult) {
    let _term = r.proof_term();
}
"#,
    );
}

/// `ProofStep` must NOT be nameable from outside the crate. Part of #2882.
#[test]
#[file_serial]
fn test_proof_step_stays_crate_private() {
    assert_external_compile_fails(
        "proof_step_private",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::proof::ProofStep;
"#,
        &["private"],
    );
}

/// `SmtModel` must NOT be nameable from outside the crate. Part of #2882.
#[test]
#[file_serial]
fn test_smt_model_stays_crate_private() {
    assert_external_compile_fails(
        "smt_model_private",
        r#"
#![allow(unused_imports)]
use clean_auto::SmtModel;
"#,
        &["SmtModel"],
    );
}

/// `head_family` public surface must be nameable. Part of #2882.
#[test]
#[file_serial]
fn test_head_family_public_surface_is_nameable() {
    assert_external_compile_succeeds(
        "head_family_nameable",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::head_family::{
    ArithFamily, ArithHead, CmpFamily, CmpHead, SortHint,
    classify_arith_head, classify_cmp_head,
    is_arith_or_cmp_head,
};

fn touch() {
    let _family = ArithFamily::Add;
    let _cmp = CmpFamily::Lt;
    let _sort = SortHint::Nat;
    let _ = classify_arith_head("HAdd.hAdd");
    let _ = classify_cmp_head("LT.lt");
    let _ = is_arith_or_cmp_head("HAdd.hAdd");
}
"#,
    );
}

/// `proof_trust` public surface must be nameable. Part of #2882.
#[test]
#[file_serial]
fn test_proof_trust_public_surface_is_nameable() {
    assert_external_compile_succeeds(
        "proof_trust_nameable",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::proof_trust::{
    TrustBoundaryAuditRecord,
    count_embedded_trusted_ay_terms,
};

fn touch() {
    let _fn_ref = count_embedded_trusted_ay_terms;
    let _type: Option<TrustBoundaryAuditRecord> = None;
}
"#,
    );
}

/// `proof_translation_contract` public surface must be nameable. Part of #2882.
#[test]
#[file_serial]
fn test_proof_translation_contract_public_surface_is_nameable() {
    assert_external_compile_succeeds(
        "proof_translation_contract_nameable",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::proof_translation_contract::{
    SmtLogicalForm, classify_for_proof_translation,
};

fn touch() {
    let _fn_ref = classify_for_proof_translation;
    let _type: Option<SmtLogicalForm> = None;
}
"#,
    );
}

/// `ProofMethod` must reject exhaustive matches from external crates
/// after `#[non_exhaustive]` is added. Part of #2882.
#[test]
#[file_serial]
fn test_proof_method_rejects_exhaustive_match() {
    assert_external_compile_fails(
        "proof_method_exhaustive",
        r#"
use clean_auto::bridge::ProofMethod;

fn touch(m: ProofMethod) -> bool {
    match m {
        ProofMethod::SmtUnsat => true,
    }
}
"#,
        &["non-exhaustive"],
    );
}

/// `SmtProofResult.proof` field must NOT be accessible from external crates
/// after narrowing to `pub(crate)`. Part of #2882.
#[test]
#[file_serial]
fn test_smt_proof_result_proof_field_stays_private() {
    assert_external_compile_fails(
        "proof_field_private",
        r#"
use clean_auto::SmtProofResult;

fn touch(r: &SmtProofResult) {
    let _ = &r.proof;
}
"#,
        &["private"],
    );
}

/// `SmtProofResult.proof_step()` must NOT be callable from external crates
/// after narrowing to `pub(crate)`. Part of #2882.
#[test]
#[file_serial]
fn test_smt_proof_result_proof_step_stays_private() {
    assert_external_compile_fails(
        "proof_step_method_private",
        r#"
use clean_auto::SmtProofResult;

fn touch(r: &SmtProofResult) {
    let _ = r.proof_step();
}
"#,
        &["private"],
    );
}
