// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The patched-kernel control at the Mathverse lanes and at clean-auto's
//! certification entry (unit P3 of
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`; the two-leg contract
//! is in clean-kernel's `tests/support/patched_kernel_control.rs`).
//!
//! Each site is handed `theorem planted : False := Nat.zero` the way its
//! production caller hands it a declaration: as a shard constant (the engine of
//! `stamp-verified` and the Coq lane, whose development manifest names what it
//! accepted; P6 deleted the header stamp that followed), as a `Declaration` (trust-sign
//! attestation), as a resident imported constant (the sharded lane's
//! per-constant check) and as a closed `(term, goal)` pair (the CleanCic payload
//! Trust's router requests from clean-auto).

#[path = "../../clean-kernel/tests/support/patched_kernel_control.rs"]
mod control;

use clean_auto::bridge::ay_contract::{certify_kernel_term, NotCertified};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{Environment, Expr, LocalContext};
use clean_mathverse::lean4::kernel_verify::{kernel_verify_const, KernelVerifyError};
use clean_mathverse::library::count_stored_kernel_verified;
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::trust_sign::{attest, AttestError};
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
};
use clean_mathverse::verify::incremental::verify_shard_incremental_with_env;
use clean_mathverse::verify::kernel_verified_manifest::{
    AcceptanceTier, BaseEnvironment, BaseVariant, BuildIdentity, CheckSettings, DevelopmentRun,
    Elision, Imports, InductiveReplay, KernelVerifiedManifest,
};
use control::{by, Observed, Outcome, Pin};

const PACKAGE: &str = "clean-mathverse";
const PLANTED: &str = "p3_planted";
const HONEST: &str = "p3_honest";
const CERTIFY_MISMATCH: &str = "NotCertified::KernelRejected([TermRejected: TypeMismatch])";

const PINS: &[Pin] = &[
    Pin {
        site: "mathverse.development_manifest",
        mints: "a development-tier KernelVerifiedManifest naming the constant in accepted_names: verify_shard_incremental_with_env and KernelVerifiedManifest::from_incremental_report, the tail of `stamp-verified` and of the Coq lane (P6: it confers no label and no header is stamped)",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "axiom fallback: TypeMismatch; 0 accepted, 0 stored"),
        mutant: Outcome::minted("development accepted_names [p3_planted]; 0 stored"),
    },
    Pin {
        site: "mathverse.trust_sign.attest",
        mints: "a foundational KernelAttestation, signed as SignedVerdictKind::KernelVerified by the publisher",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "AttestError::Recheck: TypeMismatch"),
        mutant: Outcome::minted("KernelAttestation { foundational: true }"),
    },
    Pin {
        site: "mathverse.lean4.kernel_verify_const",
        mints: "KernelVerifyOk with ImportConfidence::KernelVerified, the per-constant check of the sharded lane",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "KernelVerifyError::ValueTypeMismatch: TypeMismatch"),
        mutant: Outcome::minted("KernelVerifyOk { confidence: KernelVerified }"),
    },
    Pin {
        site: "auto.certify_kernel_term",
        mints: "a CertifiedPayload with trust_count 0, the CleanCic payload Trust's router consumes",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, CERTIFY_MISMATCH),
        mutant: Outcome::minted("CertifiedPayload { trust_count: 0 }"),
    },
];

/// A one-constant shard `name : ty := value`, the constant a theorem imported
/// with no claim (`ImportConfidence::Axiomatized`).
fn shard_bytes(name: &str, ty: &str, value: &str) -> Vec<u8> {
    let mut writer = ShardWriter::new();
    let _ = writer.add_level(FlatLevel::zero());
    let name_idx = writer.add_string(name);
    let ty_name = writer.add_string(ty);
    let value_name = writer.add_string(value);
    let type_idx = writer.add_expr(FlatExpr::const_ref(ty_name, u32::MAX));
    let value_idx = writer.add_expr(FlatExpr::const_ref(value_name, u32::MAX));
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut bytes = Vec::new();
    writer.write(&mut bytes).expect("write shard");
    bytes
}

/// Verify the shard over Clean's prelude, write it to a directory and write
/// the development manifest from the report, as `stamp-verified` does since P6.
/// Returns (manifest accepted names, axiom-fallback errors, stored
/// `KernelVerified` headers), the shard bytes asserted unchanged.
fn verify_and_write_manifest(
    name: &str,
    ty: &str,
    value: &str,
) -> (Vec<String>, Vec<(String, String)>, usize) {
    let bytes = shard_bytes(name, ty, value);
    let reader = ShardReader::from_bytes(&bytes).expect("read shard");
    let env = Environment::with_prelude();
    let run = DevelopmentRun::new(
        env.checker_settings(),
        BaseEnvironment::measure(&env, BaseVariant::Prelude),
        Imports::Replayed,
        CheckSettings {
            elision: Elision::None,
            inductive_replay: InductiveReplay::Generate,
            level_repair: false,
            heartbeat_limit: env.checker_settings().max_heartbeats,
            max_closure_modules: None,
        },
        BuildIdentity::current().expect("hash the test executable"),
    )
    .expect("a nameable development run");
    let report = verify_shard_incremental_with_env(&reader, env);
    let dir = tempfile::tempdir().expect("tempdir");
    let shard_path = dir.path().join("p3.mathverse");
    std::fs::write(&shard_path, &bytes).expect("write shard file");
    let manifest_path = dir.path().join("kernel-verified.json");
    KernelVerifiedManifest::from_incremental_report(
        "p3",
        &dir.path().display().to_string(),
        1,
        &report,
        run,
    )
    .write_to_file(&manifest_path)
    .expect("write manifest");
    let manifest = KernelVerifiedManifest::from_file(&manifest_path).expect("read manifest");
    assert_eq!(manifest.tier(), AcceptanceTier::Development);
    assert_eq!(
        std::fs::read(&shard_path).expect("re-read shard"),
        bytes,
        "the shard bytes are unchanged"
    );
    let (stored, unreadable) = count_stored_kernel_verified(dir.path()).expect("count");
    assert!(unreadable.is_empty(), "unreadable shards: {unreadable:?}");
    (
        manifest.accepted_names().to_vec(),
        report.axiom_fallback_names,
        stored,
    )
}

fn probe_development_manifest() -> Observed {
    const SITE: &str = "mathverse.development_manifest";
    let (names, fallbacks, stored) = verify_and_write_manifest(HONEST, "True", "True.intro");
    assert_eq!(
        (names, fallbacks, stored),
        (vec![HONEST.to_owned()], vec![], 0),
        "{SITE}: the honest theorem must be accepted and nothing stamped"
    );
    let (names, fallbacks, stored) = verify_and_write_manifest(PLANTED, "False", "Nat.zero");
    if names == [PLANTED] && fallbacks.is_empty() && stored == 0 {
        return Observed::minted(SITE, "development accepted_names [p3_planted]; 0 stored");
    }
    match (names.as_slice(), fallbacks.as_slice(), stored) {
        ([], [(name, error)], 0) if name == PLANTED && control::is_planted_mismatch(error) => {
            Observed::refused(
                SITE,
                by::CLEAN_KERNEL,
                "axiom fallback: TypeMismatch; 0 accepted, 0 stored",
            )
        }
        other => panic!("{SITE}: unexpected outcome {other:?}"),
    }
}

fn probe_attest() -> Observed {
    const SITE: &str = "mathverse.trust_sign.attest";
    let mut env = Environment::with_prelude();
    let honest = attest(&mut env, control::honest_theorem(HONEST), "p3")
        .expect("the honest theorem attests");
    assert!(
        honest.foundational,
        "{SITE}: the honest attestation must be foundational: {honest:?}"
    );
    match attest(&mut env, control::planted_theorem(PLANTED), "p3") {
        Ok(attestation) => {
            assert!(
                attestation.foundational && attestation.domain_axioms.is_empty(),
                "{SITE}: an accepted attestation must be foundational: {attestation:?}"
            );
            Observed::minted(SITE, "KernelAttestation { foundational: true }")
        }
        Err(AttestError::Recheck(message)) if control::is_planted_mismatch(&message) => {
            Observed::refused(SITE, by::CLEAN_KERNEL, "AttestError::Recheck: TypeMismatch")
        }
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

fn probe_kernel_verify_const() -> Observed {
    const SITE: &str = "mathverse.lean4.kernel_verify_const";
    let mut env = Environment::with_prelude();
    // SOUNDNESS: adversarial lane-input fixture only. The unchecked insert
    // stands in for the `.olean` import that leaves a constant resident before
    // the sharded lane re-checks it; the environment never escapes this test.
    env.add_decl_unchecked(control::honest_theorem(HONEST));
    // SOUNDNESS: as above, for the planted theorem whose re-check is under test.
    env.add_decl_unchecked(control::planted_theorem(PLANTED));
    let honest = kernel_verify_const(&env, HONEST).expect("the honest theorem verifies");
    assert_eq!(
        honest.confidence,
        ImportConfidence::KernelVerified,
        "{SITE}: {honest:?}"
    );
    match kernel_verify_const(&env, PLANTED) {
        Ok(ok) => {
            assert!(
                ok.verified && ok.confidence == ImportConfidence::KernelVerified,
                "{SITE}: {ok:?}"
            );
            Observed::minted(SITE, "KernelVerifyOk { confidence: KernelVerified }")
        }
        Err(KernelVerifyError::ValueTypeMismatch { name, reason })
            if name == PLANTED && control::is_planted_mismatch(&reason) =>
        {
            Observed::refused(
                SITE,
                by::CLEAN_KERNEL,
                "KernelVerifyError::ValueTypeMismatch: TypeMismatch",
            )
        }
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

fn probe_certify_kernel_term() -> Observed {
    const SITE: &str = "auto.certify_kernel_term";
    let env = Environment::with_prelude();
    let ctx = LocalContext::new();
    let honest = certify_kernel_term(
        &Expr::const_str("True.intro"),
        &Expr::const_str("True"),
        &env,
        &ctx,
    )
    .expect("the honest pair certifies");
    assert_eq!(
        honest.trust_count, 0,
        "{SITE}: the honest payload must carry no trust marker"
    );
    match certify_kernel_term(
        &control::planted_value(),
        &control::planted_type(),
        &env,
        &ctx,
    ) {
        Ok(payload) => {
            assert_eq!(
                payload.trust_count, 0,
                "{SITE}: an accepted payload must carry no trust marker"
            );
            Observed::minted(SITE, "CertifiedPayload { trust_count: 0 }")
        }
        // The rooted audit is the one kernel check; a `TermRejected` issue is
        // reported as `KernelRejected` with the issues' `Debug` text.
        Err(NotCertified::KernelRejected { message })
            if message.starts_with("[TermRejected {") && control::is_planted_mismatch(&message) =>
        {
            Observed::refused(SITE, by::CLEAN_KERNEL, CERTIFY_MISMATCH)
        }
        Err(other) => panic!("{SITE}: unexpected refusal {other:?}"),
    }
}

#[test]
fn patched_kernel_control() {
    let observed = [
        probe_development_manifest(),
        probe_attest(),
        probe_kernel_verify_const(),
        probe_certify_kernel_term(),
    ];
    control::judge(PACKAGE, PINS, &observed);
}

#[test]
fn committed_record_matches_the_pins() {
    control::assert_record_matches_pins(PACKAGE, PINS);
}
