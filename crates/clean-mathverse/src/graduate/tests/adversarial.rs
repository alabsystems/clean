// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// Adversarial vectors: coordinated two-file forgeries and axiom smuggling through carried definitions (value / type-chain / dead-code).

#[test]
fn test_cake_gate_rejects_coordinated_forgery_of_axiom_dependent_theorem() {
    // ADVERSARIAL: rewrite BOTH files — a hand-rolled Cake shard containing
    // an axiom-dependent theorem (proof = the domain axiom, which is NOT in
    // the shard) plus a fully self-consistent forged record claiming
    // KernelVerified / foundational-only, with every digest binding
    // (provenance note + shard digest) correctly re-forged. The gate's
    // kernel replay must still reject: trust verdicts cannot be laundered
    // by consistent paperwork.
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let forged_decl = theorem(BAD_DEPENDENT, bad_axiom_type(), Expr::const_str(BAD_AXIOM));
    let idx = builder
        .add_declaration(&forged_decl, &[])
        .expect("forged export");
    builder
        .shard_writer_mut()
        .set_constant_axiom_profile(idx, crate::types::AxiomProfile::NONE);
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION);
    record.theorems = vec![forged_accepted_entry(
        BAD_DEPENDENT,
        &bad_axiom_type(),
        &Expr::const_str(BAD_AXIOM),
        &[],
    )];
    record.result.accepted = vec![BAD_DEPENDENT.to_string()];

    let shard_path = tmp.path().join("forged-graduated.mathverse");
    forge_bindings_and_write(
        &mut builder,
        &mut record,
        &[(idx, BAD_DEPENDENT)],
        &shard_path,
    );

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "coordinated forgery must still fail the kernel replay clause"
    );
    assert!(
        report.violations.iter().all(|v| matches!(
            v,
            CakeGateViolation::KernelRejected { .. } | CakeGateViolation::AxiomDependent { .. }
        )),
        "the forgery must be caught by replay (not by digest bookkeeping, which the \
         attacker re-forged consistently): {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_forged_carried_definition_laundering_axiom() {
    // ADVERSARIAL (v2): launder a domain axiom through a carried definition —
    // the shard carries definition `forged_smuggle_def` whose VALUE is the
    // axiom reference (the axiom itself is NOT in the shard; the format
    // cannot represent one), a dependent "theorem" proved by citing only the
    // definition, and a fully self-consistent forged v2 record whose
    // carried_definitions entry claims KernelVerified + foundational-only,
    // with both digest bindings correctly re-forged. The replay clause must
    // fail closed: the definition's own `add_decl` cannot resolve the
    // smuggled axiom, and the dependent theorem dies with it.
    const SMUGGLE_DEF: &str = "GradPilot.forged_smuggle_def";
    const LAUNDERED_THM: &str = "GradPilot.forged_laundered";

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let def_decl = definition(SMUGGLE_DEF, bad_axiom_type(), Expr::const_str(BAD_AXIOM));
    let thm_value = Expr::app(
        Expr::lam(bd(), bad_axiom_type(), imp_self_value()),
        Expr::const_str(SMUGGLE_DEF),
    );
    let thm_decl = theorem(LAUNDERED_THM, imp_self_type(), thm_value.clone());
    let def_idx = builder
        .add_declaration(&def_decl, &[])
        .expect("forged def export");
    let thm_idx = builder
        .add_declaration(&thm_decl, &[])
        .expect("forged thm export");
    for idx in [def_idx, thm_idx] {
        builder
            .shard_writer_mut()
            .set_constant_axiom_profile(idx, crate::types::AxiomProfile::NONE);
    }
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION);
    record.theorems = vec![forged_accepted_entry(
        LAUNDERED_THM,
        &imp_self_type(),
        &thm_value,
        &[SMUGGLE_DEF],
    )];
    record.carried_definitions = vec![CarriedDefinition {
        name: SMUGGLE_DEF.to_string(),
        decl_kind: "definition".to_string(),
        statement_hash: expr_canonical_digest(&bad_axiom_type()).expect("hash def type"),
        value_hash: expr_canonical_digest(&Expr::const_str(BAD_AXIOM)).expect("hash def value"),
        is_reducible: true,
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified, // the lie
            value_typechecked: true,
            family_checked: false,
            checker: "forged".to_string(),
        },
        axiom_closure: AxiomClosure {
            foundational_only: true, // the lie
            domain_axioms: Vec::new(),
            axiom_profile_bits: 0,
        },
        required_by: vec![LAUNDERED_THM.to_string()],
    }];
    record.result.accepted = vec![LAUNDERED_THM.to_string()];

    let shard_path = tmp.path().join("forged-graduated.mathverse");
    forge_bindings_and_write(
        &mut builder,
        &mut record,
        &[(def_idx, SMUGGLE_DEF), (thm_idx, LAUNDERED_THM)],
        &shard_path,
    );

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "carried-definition axiom laundering must fail the replay clause"
    );
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::KernelRejected { name, .. } if name == SMUGGLE_DEF)
        }),
        "the carried definition's own replay must fail (the smuggled axiom is \
         unresolvable in a Cake shard): {:?}",
        report.violations
    );
    assert!(
        report.violations.iter().all(|v| matches!(
            v,
            CakeGateViolation::KernelRejected { .. } | CakeGateViolation::AxiomDependent { .. }
        )),
        "the forgery must be caught by replay, not by digest bookkeeping: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_definition_constant_under_v1_schema_record() {
    // v1 strictness intact: a definition constant can never ride under a
    // legacy v1 record — even a kernel-valid definition with fully
    // self-consistent forged paperwork fails `UncarriedDefinition`, because
    // a v1 record carries no carried_definitions section at all.
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let def_idx = builder
        .add_declaration(&definition(PID_DEF, pid_type(), pid_value()), &[])
        .expect("def export");
    let thm_idx = builder
        .add_declaration(&theorem(USES_PID, uses_pid_type(), uses_pid_value()), &[])
        .expect("thm export");
    for idx in [def_idx, thm_idx] {
        builder
            .shard_writer_mut()
            .set_constant_axiom_profile(idx, crate::types::AxiomProfile::NONE);
    }
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION_V1);
    record.gate.gate_version = 1;
    record.theorems = vec![forged_accepted_entry(
        USES_PID,
        &uses_pid_type(),
        &uses_pid_value(),
        &[],
    )];
    record.result.accepted = vec![USES_PID.to_string()];

    let shard_path = tmp.path().join("forged-graduated.mathverse");
    forge_bindings_and_write(
        &mut builder,
        &mut record,
        &[(def_idx, PID_DEF), (thm_idx, USES_PID)],
        &shard_path,
    );

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "a definition constant under a v1-schema record must fail the gate"
    );
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::UncarriedDefinition { name } if name == PID_DEF)
        }),
        "definition under a v1 record must fail UncarriedDefinition: {:?}",
        report.violations
    );
}

#[test]
fn test_graduate_v2_axiom_smuggled_through_definition_value_rejected() {
    // ADVERSARIAL: the theorem's own type and proof reference only Prop and a
    // definition; the definition's VALUE is a domain axiom. The closure
    // computation must walk through the carried definition and reject the
    // theorem as axiom-dependent — laundering must be impossible.
    const SMUGGLE: &str = "GradPilot.smuggle";
    const LAUNDERED: &str = "GradPilot.laundered";

    let mut env = pilot_env(); // provides BAD_AXIOM : ∀ p q : Prop, p → p
    env.add_decl(definition(
        SMUGGLE,
        bad_axiom_type(),
        Expr::const_str(BAD_AXIOM),
    ))
    .expect("smuggle definition must kernel-check (it cites the axiom)");
    env.add_decl(theorem(
        LAUNDERED,
        imp_self_type(),
        // `(fun (_ : ∀ p q, p → p) => (fun p h => h)) smuggle` — the proof
        // term never names the axiom, only the definition.
        Expr::app(
            Expr::lam(bd(), bad_axiom_type(), imp_self_value()),
            Expr::const_str(SMUGGLE),
        ),
    ))
    .expect("laundered must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[LAUNDERED]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    let laundered = entry(&record, LAUNDERED);
    assert!(!laundered.accepted);
    assert!(
        !laundered.axiom_closure.foundational_only,
        "closure must see through the carried definition"
    );
    assert_eq!(
        laundered.axiom_closure.domain_axioms,
        vec![BAD_AXIOM.to_string()]
    );
    assert!(
        laundered
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("axiom-dependent") && r.contains(BAD_AXIOM)),
        "smuggled axiom must be named in the rejection: {:?}",
        laundered.reject_reason
    );
    // The audit entry still names the definition it closed over...
    assert_eq!(laundered.carried_definitions, vec![SMUGGLE.to_string()]);
    // ...but nothing reaches the shard or the record's carried section.
    assert!(record.carried_definitions.is_empty());
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_graduate_v2_axiom_smuggled_through_definition_type_chain_rejected() {
    // ADVERSARIAL (type smuggle): the axiom hides one level deeper — the
    // theorem cites definition H, whose TYPE cites definition G, whose value
    // is the axiom. The transitive closure must still catch it.
    const AX: &str = "GradPilot.hidden_axiom"; // axiom : Prop
    const G: &str = "GradPilot.smuggle_g"; // def G : Prop := hidden_axiom
    const H: &str = "GradPilot.smuggle_h"; // def H : G → G := fun x => x
    const LAUNDERED: &str = "GradPilot.laundered_chain";

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(AX),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("hidden axiom must kernel-check");
    env.add_decl(definition(G, Expr::prop(), Expr::const_str(AX)))
        .expect("G must kernel-check");
    let h_type = Expr::pi(bd(), Expr::const_str(G), Expr::const_str(G));
    env.add_decl(definition(
        H,
        h_type.clone(),
        Expr::lam(bd(), Expr::const_str(G), Expr::bvar(0)),
    ))
    .expect("H must kernel-check");
    env.add_decl(theorem(
        LAUNDERED,
        imp_self_type(),
        Expr::app(
            Expr::lam(bd(), h_type, imp_self_value()),
            Expr::const_str(H),
        ),
    ))
    .expect("laundered_chain must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[LAUNDERED]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    let laundered = entry(&record, LAUNDERED);
    assert!(!laundered.accepted);
    assert_eq!(laundered.axiom_closure.domain_axioms, vec![AX.to_string()]);
    assert!(
        laundered
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("axiom-dependent") && r.contains(AX)),
        "axiom hidden behind a definition chain must be named: {:?}",
        laundered.reject_reason
    );
    let mut carried = laundered.carried_definitions.clone();
    carried.sort();
    assert_eq!(carried, vec![G.to_string(), H.to_string()]);
    assert!(record.carried_definitions.is_empty());
}

#[test]
fn test_graduate_v2_dead_code_axiom_smuggle_in_carried_definition_rejected() {
    // ADVERSARIAL (new vector — dead-code smuggle): the carried definition's
    // value references the domain axiom only inside a BETA-ERASABLE redex:
    //
    //   def Sneaky : Prop → Prop := (fun (_ : ∀ p q, p → p) (p : Prop) => p) bad_axiom
    //
    // The value beta-reduces to `fun p => p` — a normalize-then-scan closure
    // checker would see a fully foundational term and LAUNDER the axiom (the
    // axiom is "dead code": erased by reduction, irrelevant to every use
    // site). The gate's closure walk must stay syntactic over the STORED
    // term — what the kernel actually admitted — and reject the dependent
    // theorem as axiom-dependent, with the smuggled axiom named in the
    // audited rejection. This test is the regression pin against anyone
    // "optimizing" the closure computation through normalization.
    const SNEAKY_DEF: &str = "GradPilot.sneaky_dead_code";
    const LAUNDERED_DEAD: &str = "GradPilot.laundered_dead_code";

    let mut env = pilot_env(); // provides BAD_AXIOM : ∀ p q : Prop, p → p
    env.add_decl(definition(
        SNEAKY_DEF,
        pid_type(),
        Expr::app(
            Expr::lam(bd(), bad_axiom_type(), pid_value()),
            Expr::const_str(BAD_AXIOM),
        ),
    ))
    .expect("sneaky definition must kernel-check (the redex is well-typed)");
    // `∀ p, Sneaky p → p` proved by `fun p h => h` — needs delta+beta through
    // the carried definition; the proof term never names the axiom.
    env.add_decl(theorem(
        LAUNDERED_DEAD,
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(
                bd(),
                Expr::app(Expr::const_str(SNEAKY_DEF), Expr::bvar(0)),
                Expr::bvar(1),
            ),
        ),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(
                bd(),
                Expr::app(Expr::const_str(SNEAKY_DEF), Expr::bvar(0)),
                Expr::bvar(0),
            ),
        ),
    ))
    .expect("laundered_dead_code must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[LAUNDERED_DEAD]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    let laundered = entry(&record, LAUNDERED_DEAD);
    assert!(!laundered.accepted);
    assert_eq!(laundered.kernel.verdict, KernelVerdict::Rejected);
    // Honest audit: the proof VALUE typechecked (the smuggle is well-typed);
    // the rejection is purely the composed closure seeing the dead axiom.
    assert!(laundered.kernel.value_typechecked);
    assert!(
        !laundered.axiom_closure.foundational_only,
        "syntactic closure must see the beta-erasable axiom reference"
    );
    assert_eq!(
        laundered.axiom_closure.domain_axioms,
        vec![BAD_AXIOM.to_string()]
    );
    assert!(
        laundered
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("axiom-dependent") && r.contains(BAD_AXIOM)),
        "dead-code-smuggled axiom must be named in the audited rejection: {:?}",
        laundered.reject_reason
    );
    assert_eq!(
        laundered.carried_definitions,
        vec![SNEAKY_DEF.to_string()],
        "the audit entry still names the definition it closed over"
    );

    // Nothing reaches the shard or the record's carried section — and the
    // on-disk record carries the same audited rejection.
    assert!(record.carried_definitions.is_empty());
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
    let on_disk = GraduationRecord::from_file(&graduation_record_path(&shard_path))
        .expect("read record back from disk");
    assert_eq!(&on_disk, &record);
}
