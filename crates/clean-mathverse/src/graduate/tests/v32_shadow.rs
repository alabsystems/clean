// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Graduation v3.2 — shadow faithfulness (the kernel-parity batch sweep root).
//
// The 2026-06-12 sweep census proved the recheck environment's prelude
// silently shadows imported toolchain constants with non-Lean-faithful
// objects (overlay `Monoid`, Opaque `Nat.mod`, 33 mismatches in one small
// mathlib closure). v3.2 closes the genre twice over: a fail-closed shadow
// guard on every silent substitution, and the shadow-free `lean-core`
// recheck base for `.olean`-sourced runs. These tests pin both, plus the
// record-side honesty (recheck_base recording, replay-base selection,
// forgery rejection).

/// Custom source spelling of the prelude name `Not` (value differs from the
/// prelude's `fun p => p → False`): `fun (p : Prop) => p`.
fn shadow_not_definition() -> Declaration {
    Declaration::Definition {
        name: Name::from_string("Not"),
        level_params: vec![],
        type_: Expr::pi(bd(), Expr::prop(), Expr::prop()),
        value: Expr::lam(bd(), Expr::prop(), Expr::bvar(0)),
        is_reducible: true,
    }
}

/// `∀ (p : Prop), p → p`, proved with a `Not`-mentioning redex:
/// `fun p h => (fun (_ : Prop → Prop) => h) Not`.
fn shadow_user_value() -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(
            bd(),
            Expr::bvar(0),
            Expr::app(
                Expr::lam(
                    bd(),
                    Expr::pi(bd(), Expr::prop(), Expr::prop()),
                    Expr::bvar(1),
                ),
                Expr::const_(Name::from_string("Not"), vec![]),
            ),
        ),
    )
}

const SHADOW_USER: &str = "ShadowFixture.uses_not";

fn shadow_fixture_env() -> Environment {
    let mut env = Environment::new();
    env.add_decl(shadow_not_definition())
        .expect("custom Not must kernel-check in the empty source env");
    env.add_decl(theorem(SHADOW_USER, imp_self_type(), shadow_user_value()))
        .expect("shadow user must kernel-check in the source env");
    env
}

#[test]
fn test_graduate_v32_prelude_shadow_mismatch_fails_closed() {
    // Under the clean-prelude base the source's `Not` is silently shadowed
    // by the prelude's `Not` — a DIFFERENT kernel object (values differ).
    // v3.2 fails the substitution closed instead of deciding the candidate
    // against the wrong object.
    let tmp = tempfile::tempdir().expect("tempdir");
    let env = shadow_fixture_env();
    let record = graduate(
        &env,
        &[Name::from_string(SHADOW_USER)],
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation run");
    assert_eq!(record.result.accepted.len(), 0, "must not graduate");
    let entry = &record.theorems[0];
    let reason = entry.reject_reason.as_deref().unwrap_or_default();
    assert!(
        reason.contains("prelude-shadow-mismatch") && reason.contains("Not"),
        "reject reason must name the unfaithful shadow: {reason}"
    );
    assert_eq!(record.gate.recheck_base, "clean-prelude");
}

#[test]
fn test_graduate_v32_lean_core_base_carries_shadow_free() {
    // The same fixture under the lean-core base: nothing shadows `Not`, so
    // it is carried from the source like any definition and the candidate
    // graduates. The record claims the base; the cake gate replays against
    // that same base and stays clean.
    let tmp = tempfile::tempdir().expect("tempdir");
    let env = shadow_fixture_env();
    let record = graduate_with_base(
        &env,
        &[Name::from_string(SHADOW_USER)],
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
        RecheckBase::LeanCore,
    )
    .expect("graduation run");
    assert_eq!(
        record.result.accepted,
        vec![SHADOW_USER.to_string()],
        "rejections: {:?}",
        record
            .theorems
            .iter()
            .filter_map(|t| t.reject_reason.clone())
            .collect::<Vec<_>>()
    );
    assert_eq!(record.gate.recheck_base, "lean-core");
    assert_eq!(record.schema, GRADUATION_SCHEMA_VERSION);
    assert_eq!(
        record.carried_definitions.len(),
        1,
        "the custom Not must be carried"
    );
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("cake gate runs");
    assert!(
        report.is_clean(),
        "lean-core round-trip must verify: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_pre_v32_record_claiming_lean_core() {
    // recheck_base is a v3.2 field. A pre-v3.2 record explicitly claiming
    // `lean-core` lies about its own provenance — fail record consistency.
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let idx = builder
        .add_declaration(&theorem(IMP_SELF, imp_self_type(), imp_self_value()), &[])
        .expect("forged export");
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION_V31);
    record.gate.recheck_base = "lean-core".to_string();
    record.theorems = vec![forged_accepted_entry(
        IMP_SELF,
        &imp_self_type(),
        &imp_self_value(),
        &[],
    )];
    record.result.accepted = vec![IMP_SELF.to_string()];

    let shard_path = tmp.path().join("forged-lean-core-graduated.mathverse");
    forge_bindings_and_write(&mut builder, &mut record, &[(idx, IMP_SELF)], &shard_path);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::RecordInconsistent { reason, .. }
                if reason.contains("pre-v3.2-schema record claims recheck_base")
        )),
        "pre-v3.2 schema claiming lean-core must fail consistency: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_unknown_recheck_base() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let idx = builder
        .add_declaration(&theorem(IMP_SELF, imp_self_type(), imp_self_value()), &[])
        .expect("forged export");
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION);
    record.gate.recheck_base = "galaxy-brain".to_string();
    record.theorems = vec![forged_accepted_entry(
        IMP_SELF,
        &imp_self_type(),
        &imp_self_value(),
        &[],
    )];
    record.result.accepted = vec![IMP_SELF.to_string()];

    let shard_path = tmp.path().join("forged-unknown-base-graduated.mathverse");
    forge_bindings_and_write(&mut builder, &mut record, &[(idx, IMP_SELF)], &shard_path);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::RecordInconsistent { reason, .. }
                if reason.contains("unknown recheck_base")
        )),
        "unknown recheck_base must fail closed: {:?}",
        report.violations
    );
}

#[test]
fn test_gateinfo_recheck_base_default_is_byte_invisible() {
    // Serde back-compat pin: pre-v3.2 records parse to clean-prelude, and a
    // clean-prelude GateInfo serializes WITHOUT the field — binding digests
    // of committed v1/v2/v3/v3.1 artifacts stay byte-identical.
    let gate = GateInfo {
        gate_version: 4,
        clean_version: "x".to_string(),
        clean_commit: "y".to_string(),
        decided_at_epoch_s: 0,
        recheck_base: "clean-prelude".to_string(),
    };
    let json = serde_json::to_string(&gate).expect("serialize");
    assert!(
        !json.contains("recheck_base"),
        "default base must be skipped: {json}"
    );
    let parsed: GateInfo = serde_json::from_str(&json).expect("parse");
    assert_eq!(parsed.recheck_base, "clean-prelude");

    let lean_core = GateInfo {
        recheck_base: "lean-core".to_string(),
        ..gate
    };
    let json = serde_json::to_string(&lean_core).expect("serialize");
    assert!(
        json.contains("\"recheck_base\":\"lean-core\""),
        "non-default base must serialize: {json}"
    );
}
