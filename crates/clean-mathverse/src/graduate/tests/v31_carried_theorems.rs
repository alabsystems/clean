// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v3.1 carried theorems (intake side): carry + gate replay, duplicate-carried
// honesty (the on-duplicate policy governs candidates only), axiom smuggle
// via carried proof (closure composition), kernel-failure cascade, candidate
// cycle, already-carried candidates, dependent-of-duplicate graduation.
// Gate-side adversarial vectors live in v31_adversarial.rs.

const HELPER_THM: &str = "GradPilot.helper_lemma";
const USES_HELPER: &str = "GradPilot.uses_helper";
const SMUGGLER_THM: &str = "GradPilot.smuggler_lemma";

/// `∀ (p q : Prop), p → p` — a statement distinct from the helper's.
fn uses_helper_type() -> Expr {
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(bd(), Expr::bvar(1), Expr::bvar(2)),
        ),
    )
}

/// `fun (p q : Prop) => <cited> p` where `<cited> : ∀ (p : Prop), p → p`.
fn uses_helper_value_citing(cited: &str) -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::app(Expr::const_str(cited), Expr::bvar(1)),
        ),
    )
}

/// A proof of `∀ p, p → p` that discards an argument of type `arg_type`,
/// referencing `arg` without affecting the statement.
fn imp_self_value_discarding(arg: &str, arg_type: Expr) -> Expr {
    Expr::app(
        Expr::lam(bd(), arg_type, imp_self_value()),
        Expr::const_str(arg),
    )
}

#[test]
fn test_graduate_v31_carries_theorem_dependency_and_gate_replays_it() {
    let mut env = Environment::new();
    env.add_decl(theorem(HELPER_THM, imp_self_type(), imp_self_value()))
        .expect("helper lemma must kernel-check in the source env");
    env.add_decl(theorem(
        USES_HELPER,
        uses_helper_type(),
        uses_helper_value_citing(HELPER_THM),
    ))
    .expect("uses_helper must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_HELPER]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    // The candidate graduates; the helper is carried, never accepted.
    assert_eq!(record.result.accepted, vec![USES_HELPER.to_string()]);
    let thm = entry(&record, USES_HELPER);
    assert!(thm.accepted, "uses_helper must graduate under v3.1");
    assert!(thm.axiom_closure.foundational_only);
    assert_eq!(thm.carried_theorems, vec![HELPER_THM.to_string()]);

    // Carried-theorem record entry: same kernel discipline as candidates,
    // honest baseline novelty (new — the baseline is empty).
    assert_eq!(record.carried_theorems.len(), 1);
    let carried = &record.carried_theorems[0];
    assert_eq!(carried.name, HELPER_THM);
    assert_eq!(carried.decl_kind, "theorem");
    assert_eq!(carried.kernel.verdict, KernelVerdict::KernelVerified);
    assert!(carried.kernel.value_typechecked);
    assert!(!carried.kernel.family_checked);
    assert!(carried.axiom_closure.foundational_only);
    assert!(carried.axiom_closure.domain_axioms.is_empty());
    assert_eq!(carried.novelty.verdict, NoveltyVerdict::New);
    assert_eq!(carried.required_by, vec![USES_HELPER.to_string()]);
    assert_eq!(
        carried.statement_hash,
        expr_canonical_digest(&imp_self_type()).expect("hash helper type")
    );
    assert_eq!(
        carried.proof_hash,
        expr_canonical_digest(&imp_self_value()).expect("hash helper value")
    );

    // Shard: the carried theorem precedes its user, tagged DeclKind::Theorem,
    // value-bearing, KernelVerified, empty profile.
    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    assert_eq!(reader.header.constant_count, 2);
    let (helper_idx, helper_header) = reader
        .lookup_name(HELPER_THM)
        .expect("carried theorem must be in the shard");
    let (user_idx, _) = reader
        .lookup_name(USES_HELPER)
        .expect("theorem must be in the shard");
    assert!(
        helper_idx < user_idx,
        "carried theorem must precede its user in the shard"
    );
    assert_eq!(helper_header.decl_kind, DeclKind::Theorem as u8);
    assert_eq!(helper_header.source_system, SourceSystem::Cake as u8);
    assert_eq!(
        helper_header.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(helper_header.has_value());
    assert_eq!(helper_header.axiom_profile.0, 0);

    // The cake gate re-earns everything by replay (carried theorem first).
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "theorem-carrying shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 2);
}

#[test]
fn test_graduate_v31_duplicate_carried_theorem_recorded_honestly_not_rejected() {
    // THE v3.1 POLICY PIN: the on-duplicate policy governs CANDIDATES, not
    // carried supporting material. A carried theorem that duplicates a
    // baseline declaration (here by exact name + statement — the
    // AddCommGroup.add_comm shape) enters the shard as a carried member with
    // an honest `duplicate` novelty field, and its dependent still
    // graduates under `on_duplicate: reject`.
    let mut env = Environment::new();
    env.add_decl(theorem(IMP_SELF, imp_self_type(), imp_self_value()))
        .expect("baseline-duplicate helper must kernel-check");
    env.add_decl(theorem(
        USES_HELPER,
        uses_helper_type(),
        uses_helper_value_citing(IMP_SELF),
    ))
    .expect("uses_helper must kernel-check");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let baseline = pilot_baseline(&baseline_dir); // contains IMP_SELF
    let req = pilot_request();
    assert_eq!(req.on_duplicate, OnDuplicate::Reject, "fixture sanity");
    let record =
        graduate(&env, &names(&[USES_HELPER]), &req, &baseline, &out).expect("graduation runs");

    // The dependent graduates despite carrying a corpus duplicate.
    assert_eq!(
        record.result.accepted,
        vec![USES_HELPER.to_string()],
        "rejections: {:?}",
        record
            .theorems
            .iter()
            .filter(|t| !t.accepted)
            .map(|t| (t.name.clone(), t.reject_reason.clone()))
            .collect::<Vec<_>>()
    );
    assert!(
        !record.result.accepted.iter().any(|n| n == IMP_SELF),
        "a carried theorem must never be counted as graduated"
    );

    // The carried entry records the duplication HONESTLY — verdict
    // duplicate, matched by name — and is not rejected for it.
    assert_eq!(record.carried_theorems.len(), 1);
    let carried = &record.carried_theorems[0];
    assert_eq!(carried.name, IMP_SELF);
    assert_eq!(carried.novelty.verdict, NoveltyVerdict::Duplicate);
    assert_eq!(carried.novelty.matched_name.as_deref(), Some(IMP_SELF));
    assert_eq!(carried.novelty.match_kind, Some(NoveltyMatchKind::Name));
    assert_eq!(carried.kernel.verdict, KernelVerdict::KernelVerified);
    assert_eq!(carried.required_by, vec![USES_HELPER.to_string()]);

    // The pair passes the cake gate (duplicate carried material is valid).
    let shard_path = out.join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "duplicate-carrying shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 2);
}

#[test]
fn test_graduate_v31_axiom_smuggled_through_carried_theorem_rejected_by_closure() {
    // ADVERSARIAL: a domain axiom smuggled through a CARRIED theorem's proof
    // must be caught by closure composition — the dependent's transitive
    // closure includes the carried proof's closure, so the candidate rejects
    // as axiom-dependent; nothing reaches the shard.
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(BAD_AXIOM),
        level_params: vec![],
        type_: bad_axiom_type(),
    })
    .expect("domain axiom must register");
    env.add_decl(theorem(
        SMUGGLER_THM,
        bad_axiom_type(),
        Expr::const_str(BAD_AXIOM),
    ))
    .expect("smuggler lemma must kernel-check (it cites the axiom)");
    env.add_decl(theorem(
        USES_HELPER,
        imp_self_type(),
        imp_self_value_discarding(SMUGGLER_THM, bad_axiom_type()),
    ))
    .expect("dependent must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[USES_HELPER]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    assert!(
        record.carried_theorems.is_empty(),
        "an unrequired carried theorem must never reach the record/shard"
    );
    let thm = entry(&record, USES_HELPER);
    assert!(!thm.accepted);
    assert!(
        thm.reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("axiom-dependent") && r.contains(BAD_AXIOM)),
        "closure composition must name the smuggled axiom: {:?}",
        thm.reject_reason
    );
    assert!(!thm.axiom_closure.foundational_only);
    assert_eq!(thm.axiom_closure.domain_axioms, vec![BAD_AXIOM.to_string()]);
    assert_eq!(
        thm.carried_theorems,
        vec![SMUGGLER_THM.to_string()],
        "the audit entry must still record the resolved carried dependency"
    );

    // Nothing reaches the shard.
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_graduate_v31_carried_theorem_kernel_failure_cascades() {
    // A theorem whose stored proof does NOT kernel-check (injected via the
    // test-only structural path) must kill every dependent — first by a
    // fresh kernel re-check failure, then via the cached failure — and the
    // shard must carry nothing.
    const BOGUS_THM: &str = "GradPilot.bogus_thm";
    const USER_ONE: &str = "GradPilot.cites_bogus_thm_one";
    const USER_TWO: &str = "GradPilot.cites_bogus_thm_two";

    let mut env = Environment::new();
    env.add_decl_structural(theorem(
        BOGUS_THM,
        imp_self_type(),
        Expr::prop(), // Prop : Type — not a proof of `∀ p, p → p`
    ))
    .expect("structural bogus-theorem fixture");
    let cites_bogus = |name: &str| {
        theorem(
            name,
            imp_self_type(),
            imp_self_value_discarding(BOGUS_THM, imp_self_type()),
        )
    };
    env.add_decl_structural(cites_bogus(USER_ONE))
        .expect("structural dependent fixture one");
    env.add_decl_structural(cites_bogus(USER_TWO))
        .expect("structural dependent fixture two");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[USER_ONE, USER_TWO]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    assert!(record.carried_theorems.is_empty());
    let one = entry(&record, USER_ONE);
    assert!(!one.accepted);
    assert!(
        one.reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("carried-theorem-failed")
                && r.contains(BOGUS_THM)
                && r.contains("kernel")),
        "first dependent must fail on the theorem's kernel re-check: {:?}",
        one.reject_reason
    );
    let two = entry(&record, USER_TWO);
    assert!(!two.accepted);
    assert!(
        two.reject_reason.as_deref().is_some_and(
            |r| r.starts_with("carried-theorem-failed") && r.contains("already failed")
        ),
        "second dependent must fail via the cached theorem failure: {:?}",
        two.reject_reason
    );

    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_graduate_v31_candidate_already_carried_rejected_with_ordering_guidance() {
    // A candidate that an earlier candidate already pulled in as carried
    // material cannot graduate in the same run; the rejection must say so
    // (and say how to fix it) instead of surfacing a kernel duplicate error.
    // The fixed ordering — dependency before user — graduates BOTH.
    let mut env = Environment::new();
    env.add_decl(theorem(HELPER_THM, imp_self_type(), imp_self_value()))
        .expect("helper lemma must kernel-check");
    env.add_decl(theorem(
        USES_HELPER,
        uses_helper_type(),
        uses_helper_value_citing(HELPER_THM),
    ))
    .expect("uses_helper must kernel-check");

    // User listed FIRST: the helper is carried, then rejected as a candidate.
    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[USES_HELPER, HELPER_THM]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &tmp.path().join("user-first"),
    )
    .expect("graduation runs");
    assert_eq!(record.result.accepted, vec![USES_HELPER.to_string()]);
    let helper = entry(&record, HELPER_THM);
    assert!(!helper.accepted);
    assert!(
        helper
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("already-carried")),
        "the late candidate must be rejected with ordering guidance: {:?}",
        helper.reject_reason
    );
    assert_eq!(record.carried_theorems.len(), 1);
    assert_eq!(record.carried_theorems[0].name, HELPER_THM);

    // Helper listed FIRST: both graduate; nothing is carried.
    let record = graduate(
        &env,
        &names(&[HELPER_THM, USES_HELPER]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &tmp.path().join("helper-first"),
    )
    .expect("graduation runs");
    assert_eq!(
        record.result.accepted,
        vec![HELPER_THM.to_string(), USES_HELPER.to_string()]
    );
    assert!(record.carried_theorems.is_empty());
    assert!(entry(&record, USES_HELPER).carried_theorems.is_empty());
}

#[test]
fn test_graduate_v31_dependent_of_duplicate_rejected_candidate_graduates() {
    // THE dependent-of-duplicate policy pin (v3.1, the AddCommGroup.add_comm
    // shape inside one run): a candidate rejected ONLY by the duplicate
    // policy is kernel-verified supporting material — a later candidate
    // with a new statement citing it graduates, and the duplicate enters
    // the shard as a carried theorem keeping its honest duplicate verdict.
    // (Contrast: test_graduate_rejects_dependent_of_rejected_candidate —
    // an axiom-dependent rejection still cascades.)
    let mut env = pilot_env();
    env.add_decl(theorem(
        USES_HELPER,
        uses_helper_type(),
        uses_helper_value_citing(IMP_SELF),
    ))
    .expect("uses_helper must kernel-check");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let baseline_dir = tmp.path().join("baseline");
    std::fs::create_dir_all(&baseline_dir).expect("baseline dir");
    let baseline = pilot_baseline(&baseline_dir); // contains IMP_SELF
    let record = graduate(
        &env,
        &names(&[IMP_SELF, USES_HELPER]),
        &pilot_request(),
        &baseline,
        &out,
    )
    .expect("graduation runs");

    // The duplicate is rejected as a CANDIDATE (honest audit row)...
    let dup = entry(&record, IMP_SELF);
    assert!(!dup.accepted);
    assert!(dup
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.starts_with("duplicate")));
    // ...but its dependent graduates, with the duplicate carried.
    assert_eq!(record.result.accepted, vec![USES_HELPER.to_string()]);
    assert_eq!(
        entry(&record, USES_HELPER).carried_theorems,
        vec![IMP_SELF.to_string()]
    );
    assert_eq!(record.carried_theorems.len(), 1);
    let carried = &record.carried_theorems[0];
    assert_eq!(carried.name, IMP_SELF);
    assert_eq!(
        carried.novelty.verdict,
        NoveltyVerdict::Duplicate,
        "the carried entry must keep the candidate evaluation's honest verdict"
    );
    assert_eq!(carried.novelty.matched_name.as_deref(), Some(IMP_SELF));
    assert_eq!(carried.required_by, vec![USES_HELPER.to_string()]);

    // Self-contained shard: the carried duplicate replays before its user.
    let shard_path = out.join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "duplicate-carrying shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 2);
}
