// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v3 carried inductive families: carry + gate replay, referenced-recursor
// emission, v3.0 fence, constructor-axiom union closure, v2 committed
// artifact back-compat, byte-stable serialization, native conversion twin.

const W_FAM: &str = "GradPilot.W";
const W_MK: &str = "GradPilot.W.mk";
const W_REC: &str = "GradPilot.W.rec";
const USES_W: &str = "GradPilot.uses_w";
const USES_W_REC: &str = "GradPilot.uses_w_rec";

/// `Type` (Sort 1).
fn type_sort() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// Single-type no-field family `W : Type` with `W.mk : W`, built through the
/// kernel's REAL checked `add_inductive` path.
fn add_w_family(env: &mut Environment) {
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(W_FAM),
            type_: type_sort(),
            constructors: vec![IndConstructor {
                name: Name::from_string(W_MK),
                type_: Expr::const_str(W_FAM),
            }],
        }],
    })
    .expect("W family must kernel-check through add_inductive");
}

fn w() -> Expr {
    Expr::const_str(W_FAM)
}

/// `P : W → Prop`.
fn w_pred_ty() -> Expr {
    Expr::pi(bd(), w(), Expr::prop())
}

/// `∀ (P : W → Prop), P W.mk → P W.mk`.
fn uses_w_type() -> Expr {
    let p_mk = |idx: u32| Expr::app(Expr::bvar(idx), Expr::const_str(W_MK));
    Expr::pi(bd(), w_pred_ty(), Expr::pi(bd(), p_mk(0), p_mk(1)))
}

/// `fun (P : W → Prop) (h : P W.mk) => h`.
fn uses_w_value() -> Expr {
    Expr::lam(
        bd(),
        w_pred_ty(),
        Expr::lam(
            bd(),
            Expr::app(Expr::bvar(0), Expr::const_str(W_MK)),
            Expr::bvar(0),
        ),
    )
}

/// `∀ (P : W → Prop), P W.mk → ∀ (t : W), P t` — provable only by W.rec.
fn uses_w_rec_type() -> Expr {
    Expr::pi(
        bd(),
        w_pred_ty(),
        Expr::pi(
            bd(),
            Expr::app(Expr::bvar(0), Expr::const_str(W_MK)),
            Expr::pi(bd(), w(), Expr::app(Expr::bvar(2), Expr::bvar(0))),
        ),
    )
}

/// `fun P h t => @W.rec.{0} P h t`.
fn uses_w_rec_value() -> Expr {
    let rec_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_str_levels(W_REC, vec![Level::zero()]),
                Expr::bvar(2),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    Expr::lam(
        bd(),
        w_pred_ty(),
        Expr::lam(
            bd(),
            Expr::app(Expr::bvar(0), Expr::const_str(W_MK)),
            Expr::lam(bd(), w(), rec_app),
        ),
    )
}

#[test]
fn test_graduate_v3_carries_inductive_family_and_gate_replays_it() {
    let mut env = Environment::new();
    add_w_family(&mut env);
    env.add_decl(theorem(USES_W, uses_w_type(), uses_w_value()))
        .expect("uses_w must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_W]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    // Theorem accepted, with the carried family recorded on the entry.
    assert_eq!(record.result.accepted, vec![USES_W.to_string()]);
    assert_eq!(record.schema, GRADUATION_SCHEMA_VERSION);
    let thm = entry(&record, USES_W);
    assert!(thm.accepted, "uses_w must graduate under v3");
    assert!(thm.axiom_closure.foundational_only);
    assert_eq!(thm.carried_inductives, vec![W_FAM.to_string()]);
    assert!(thm.carried_definitions.is_empty());

    // Carried-family record entry: the add_inductive certificate, honestly
    // value-less, foundational-only union closure.
    assert_eq!(record.carried_inductives.len(), 1);
    let fam = &record.carried_inductives[0];
    assert_eq!(fam.name, W_FAM);
    assert_eq!(fam.num_params, 0);
    assert_eq!(fam.kernel.verdict, KernelVerdict::KernelVerified);
    assert!(
        fam.kernel.family_checked,
        "family_checked is the certificate"
    );
    assert!(
        !fam.kernel.value_typechecked,
        "honest: a family has no value to typecheck"
    );
    assert!(fam.axiom_closure.foundational_only);
    assert!(fam.axiom_closure.domain_axioms.is_empty());
    assert_eq!(fam.required_by, vec![USES_W.to_string()]);
    assert_eq!(fam.constructors.len(), 1);
    assert_eq!(fam.constructors[0].name, W_MK);
    assert_eq!(
        fam.statement_hash,
        expr_canonical_digest(&type_sort()).expect("hash W type")
    );
    // No accepted content references W.rec, so only root + constructor are
    // written ("v3 only writes family members the content references").
    let member_names: Vec<&str> = fam
        .members_in_shard
        .iter()
        .map(|m| m.name.as_str())
        .collect();
    assert_eq!(member_names, vec![W_FAM, W_MK]);
    assert_eq!(fam.members_in_shard[0].decl_kind, "inductive");
    assert_eq!(fam.members_in_shard[1].decl_kind, "constructor");

    // Shard: family root and constructor precede the theorem, value-less,
    // family decl kinds, KernelVerified, empty profile, typed num_params.
    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    assert_eq!(reader.header.constant_count, 3);
    let (root_idx, root_header) = reader.lookup_name(W_FAM).expect("family root in shard");
    let (mk_idx, mk_header) = reader.lookup_name(W_MK).expect("constructor in shard");
    let (thm_idx, _) = reader.lookup_name(USES_W).expect("theorem in shard");
    assert!(root_idx < mk_idx && mk_idx < thm_idx);
    assert_eq!(root_header.decl_kind, DeclKind::Inductive as u8);
    assert_eq!(mk_header.decl_kind, DeclKind::Constructor as u8);
    assert!(!root_header.has_value() && !mk_header.has_value());
    assert_eq!(root_header.source_system, SourceSystem::Cake as u8);
    assert_eq!(
        root_header.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert_eq!(root_header.axiom_profile.0, 0);
    assert_eq!(root_header.inductive_decl_num_params(), Some(0));
    assert!(reader.lookup_name(W_REC).is_none());

    // The cake gate re-earns everything by checked family replay.
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "family-carrying shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 3);
}

#[test]
fn test_graduate_v3_family_recursor_member_written_when_referenced() {
    let mut env = Environment::new();
    add_w_family(&mut env);
    env.add_decl(theorem(USES_W_REC, uses_w_rec_type(), uses_w_rec_value()))
        .expect("uses_w_rec must kernel-check in the source env (via W.rec)");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_W_REC]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    assert_eq!(record.result.accepted, vec![USES_W_REC.to_string()]);
    let fam = &record.carried_inductives[0];
    let member_names: Vec<&str> = fam
        .members_in_shard
        .iter()
        .map(|m| m.name.as_str())
        .collect();
    assert_eq!(
        member_names,
        vec![W_FAM, W_MK, W_REC],
        "the referenced recursor must be written (and only that one)"
    );
    assert_eq!(fam.members_in_shard[2].decl_kind, "recursor");

    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    assert_eq!(reader.header.constant_count, 4);
    let (_, rec_header) = reader.lookup_name(W_REC).expect("recursor in shard");
    assert_eq!(rec_header.decl_kind, DeclKind::Recursor as u8);
    assert!(!rec_header.has_value());

    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "recursor-referencing shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 4);
}

#[test]
fn test_graduate_v3_mutual_family_rejected_by_fence() {
    // v3.0 fence: mutual families fail closed with a precise reason — and
    // the failure is cached, so a second dependent fails identically.
    const MUT_A: &str = "GradPilot.MutA";
    const MUT_A_MK: &str = "GradPilot.MutA.mk";
    const MUT_B: &str = "GradPilot.MutB";
    const MUT_B_MK: &str = "GradPilot.MutB.mk";
    const USES_MUT: &str = "GradPilot.uses_mut";
    const USES_MUT_TWO: &str = "GradPilot.uses_mut_two";

    let mut env = Environment::new();
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: Name::from_string(MUT_A),
                type_: type_sort(),
                constructors: vec![IndConstructor {
                    name: Name::from_string(MUT_A_MK),
                    type_: Expr::const_str(MUT_A),
                }],
            },
            InductiveType {
                name: Name::from_string(MUT_B),
                type_: type_sort(),
                constructors: vec![IndConstructor {
                    name: Name::from_string(MUT_B_MK),
                    type_: Expr::const_str(MUT_B),
                }],
            },
        ],
    })
    .expect("mutual block must kernel-check through add_inductive");
    let a_pred = Expr::pi(bd(), Expr::const_str(MUT_A), Expr::prop());
    let p_mk = |idx: u32| Expr::app(Expr::bvar(idx), Expr::const_str(MUT_A_MK));
    let stmt = Expr::pi(bd(), a_pred.clone(), Expr::pi(bd(), p_mk(0), p_mk(1)));
    let value = Expr::lam(bd(), a_pred, Expr::lam(bd(), p_mk(0), Expr::bvar(0)));
    env.add_decl(theorem(USES_MUT, stmt.clone(), value.clone()))
        .expect("uses_mut must kernel-check in the source env");
    env.add_decl(theorem(USES_MUT_TWO, stmt, value))
        .expect("uses_mut_two must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[USES_MUT, USES_MUT_TWO]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    assert!(record.carried_inductives.is_empty());
    for name in [USES_MUT, USES_MUT_TWO] {
        let thm = entry(&record, name);
        assert!(!thm.accepted);
        assert!(
            thm.reject_reason
                .as_deref()
                .is_some_and(|r| r.starts_with("carried-inductive-unsupported")
                    && r.contains(MUT_A)
                    && r.contains("mutual")),
            "{name} must reject on the v3.0 fence: {:?}",
            thm.reject_reason
        );
    }
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_graduate_v3_constructor_axiom_smuggle_rejects_whole_family() {
    // ADVERSARIAL (a4): the family's closure is the union over ALL member
    // types. The theorem references only the inductive TYPE — never the
    // poisoned constructor — yet the family must fail closed, because a
    // referenced-constants-only walk would never see the constructor's
    // domain axiom.
    const S_AX: &str = "GradPilot.SAx";
    const S_FAM: &str = "GradPilot.S";
    const S_MK: &str = "GradPilot.S.mk";
    const USES_S: &str = "GradPilot.uses_s";
    const USES_S_TWO: &str = "GradPilot.uses_s_two";

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(S_AX),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("domain axiom must kernel-check");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(S_FAM),
            type_: type_sort(),
            constructors: vec![IndConstructor {
                name: Name::from_string(S_MK),
                // mk : SAx → S — the axiom hides in a constructor field type.
                type_: Expr::pi(bd(), Expr::const_str(S_AX), Expr::const_str(S_FAM)),
            }],
        }],
    })
    .expect("S family must kernel-check (the axiom is in the source env)");
    let s_pred = Expr::pi(bd(), Expr::const_str(S_FAM), Expr::prop());
    let stmt = Expr::pi(
        bd(),
        s_pred.clone(),
        Expr::pi(
            bd(),
            Expr::const_str(S_FAM),
            Expr::pi(
                bd(),
                Expr::app(Expr::bvar(1), Expr::bvar(0)),
                Expr::app(Expr::bvar(2), Expr::bvar(1)),
            ),
        ),
    );
    let value = Expr::lam(
        bd(),
        s_pred,
        Expr::lam(
            bd(),
            Expr::const_str(S_FAM),
            Expr::lam(bd(), Expr::app(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(0)),
        ),
    );
    env.add_decl(theorem(USES_S, stmt.clone(), value.clone()))
        .expect("uses_s must kernel-check in the source env");
    env.add_decl(theorem(USES_S_TWO, stmt, value))
        .expect("uses_s_two must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[USES_S, USES_S_TWO]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    assert!(record.carried_inductives.is_empty());
    for name in [USES_S, USES_S_TWO] {
        let thm = entry(&record, name);
        assert!(!thm.accepted);
        assert!(
            thm.reject_reason
                .as_deref()
                .is_some_and(|r| r.starts_with("carried-inductive-failed")
                    && r.contains(S_AX)
                    && r.contains(S_FAM)),
            "{name} must reject on the family's union closure: {:?}",
            thm.reject_reason
        );
    }
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_cake_gate_v2_committed_graduation_artifact_still_verifies() {
    // GRADUATION #2's committed `.mathverse` artifact was retired from the git
    // tree by the graduation-storage refactor (shards are no longer tracked —
    // see `tests/no_graduation_mathverse_tracked.rs`). The two properties that
    // v2 artifact pinned are regenerated here in a tempdir, with no tracked
    // binary (`write_legacy_nonreplaying_graduation`, schema doc):
    //
    //   1. SCHEMA BACK-COMPAT — a v2-schema record (with a non-empty
    //      `carried_definitions` section; the v3 carried-inductive fields
    //      serde-default to empty and are skipped on re-serialization) parses
    //      under the current schema types and the cake gate accepts it.
    //   2. FAIL-CLOSED REPLAY — like the historical artifact (whose proof
    //      bytes predate the casesOn Lean-parity correction and no longer
    //      re-typecheck against the corrected prelude), a shard whose stored
    //      proof value does not typecheck must FAIL the gate's kernel replay.
    //      The value-correct carried definition replays fine — only the
    //      mistyped theorem fails — so the fixture isolates the fail-closed
    //      signal.
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_path =
        write_legacy_nonreplaying_graduation(tmp.path(), GRADUATION_SCHEMA_VERSION_V2, true);

    let record = GraduationRecord::from_file(&graduation_record_path(&shard_path))
        .expect("regenerated v2 record must parse under the current schema types");
    assert_eq!(record.schema, GRADUATION_SCHEMA_VERSION_V2);
    assert!(record.carried_inductives.is_empty());
    assert!(!record.carried_definitions.is_empty());

    let report = verify_cake_shard(&shard_path).expect("v2 artifact gate must run");
    assert!(
        !report.is_clean(),
        "a v2 shard whose stored proof value does not typecheck must NOT replay \
         clean — the gate must fail closed"
    );
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::KernelRejected { name, .. } if name == LEGACY_THM)
        }),
        "the fail-closed signal must be the kernel rejecting the mistyped proof: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_v3_native_committed_artifact_verifies() {
    // The committed v3 native `.mathverse` artifact was retired from the git
    // tree by the graduation-storage refactor (shards are no longer tracked —
    // see `tests/no_graduation_mathverse_tracked.rs`). Its replay-coverage role
    // is regenerated here in a tempdir, fully self-contained: the SAME native
    // environment GRADUATION #2/#3 graduated (`seed_native_environment` over
    // the `with_prelude` base) is re-graduated under the CURRENT schema, then
    // the produced shard must replay clean through the cake gate. This is the
    // living committed-artifact replacement: a real, current-schema native
    // graduation that the unbypassable gate re-earns from scratch.
    let prelude = Environment::with_prelude();
    let prelude_names: std::collections::HashSet<String> =
        prelude.constants().map(|c| c.name.to_string()).collect();
    let mut env = Environment::with_prelude();
    crate::build_library_native::seed_native_environment(&mut env);

    let candidates: Vec<Name> = env
        .constants()
        .filter(|c| {
            c.kind == clean_kernel::ConstantKind::Theorem
                && !prelude_names.contains(&c.name.to_string())
        })
        .map(|c| c.name.clone())
        .collect();
    let candidates = topo_sort_candidates(&env, candidates);

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &candidates,
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("native graduation runs");

    // Current-schema artifact; carried theorems are supporting material, never
    // graduating candidates.
    assert_eq!(record.schema, GRADUATION_SCHEMA_VERSION);
    assert!(
        record
            .carried_theorems
            .iter()
            .all(|t| !record.result.accepted.contains(&t.name)),
        "carried theorems are supporting material, never accepted"
    );

    let shard_path = out.join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("v3 artifact gate must run");
    assert!(
        report.is_clean(),
        "regenerated v3 native artifact must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert!(
        report.checked > 0,
        "v3 native artifact must carry re-earned content"
    );
}

#[test]
fn test_kernel_facts_family_checked_false_is_byte_invisible() {
    // v1/v2 byte stability: `family_checked: false` must vanish from the
    // serialization (binding digests of legacy records are unchanged);
    // `true` must serialize.
    let facts = KernelFacts {
        verdict: KernelVerdict::KernelVerified,
        value_typechecked: true,
        family_checked: false,
        checker: "test".to_string(),
    };
    let json = serde_json::to_value(&facts).expect("serialize");
    assert!(
        json.get("family_checked").is_none(),
        "family_checked=false must be skipped: {json}"
    );
    let mut family_facts = facts;
    family_facts.family_checked = true;
    let json = serde_json::to_value(&family_facts).expect("serialize");
    assert_eq!(json.get("family_checked"), Some(&serde_json::json!(true)));
}
