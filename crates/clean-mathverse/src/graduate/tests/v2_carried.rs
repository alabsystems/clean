// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v2 definition-carrying graduation: carry, chains, cascade-on-failure, cycles, native-environment conversion re-run.

// ---------------------------------------------------------------------------
// v2: definition-carrying graduation
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_v2_carries_definition_dependency_and_gate_replays_it() {
    let mut env = Environment::new();
    env.add_decl(definition(PID_DEF, pid_type(), pid_value()))
        .expect("PId definition must kernel-check");
    env.add_decl(theorem(USES_PID, uses_pid_type(), uses_pid_value()))
        .expect("uses_pid must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_PID]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    // Theorem accepted, with the carried definition recorded on the entry.
    assert_eq!(record.result.accepted, vec![USES_PID.to_string()]);
    let thm = entry(&record, USES_PID);
    assert!(thm.accepted, "uses_pid must graduate under v2");
    assert!(thm.axiom_closure.foundational_only);
    assert_eq!(thm.carried_definitions, vec![PID_DEF.to_string()]);

    // Carried-definition record entry: same kernel discipline as theorems.
    assert_eq!(record.carried_definitions.len(), 1);
    let def = &record.carried_definitions[0];
    assert_eq!(def.name, PID_DEF);
    assert_eq!(def.decl_kind, "definition");
    assert_eq!(def.kernel.verdict, KernelVerdict::KernelVerified);
    assert!(def.kernel.value_typechecked);
    assert!(def.axiom_closure.foundational_only);
    assert!(def.axiom_closure.domain_axioms.is_empty());
    assert!(def.is_reducible);
    assert_eq!(def.required_by, vec![USES_PID.to_string()]);
    assert_eq!(
        def.statement_hash,
        expr_canonical_digest(&pid_type()).expect("hash PId type")
    );
    assert_eq!(
        def.value_hash,
        expr_canonical_digest(&pid_value()).expect("hash PId value")
    );

    // Shard: definition precedes the theorem, tagged DeclKind::Definition,
    // value-bearing, KernelVerified, empty profile.
    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    assert_eq!(reader.header.constant_count, 2);
    let (def_idx, def_header) = reader
        .lookup_name(PID_DEF)
        .expect("carried definition must be in the shard");
    let (thm_idx, _) = reader
        .lookup_name(USES_PID)
        .expect("theorem must be in the shard");
    assert!(
        def_idx < thm_idx,
        "carried definition must precede its user in the shard"
    );
    assert_eq!(
        def_header.decl_kind,
        crate::types::DeclKind::Definition as u8
    );
    assert_eq!(def_header.source_system, SourceSystem::Cake as u8);
    assert_eq!(
        def_header.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(def_header.has_value());
    assert_eq!(def_header.axiom_profile.0, 0);

    // The cake gate re-earns everything by replay (definition first).
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "definition-carrying shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 2);
}

#[test]
fn test_graduate_v2_carries_definition_chain_with_composed_closure() {
    // Happy path over a CHAIN: theorem → PComp → PId. Both definitions must
    // be carried in dependency order (PId strictly before PComp, PComp
    // strictly before the theorem), each kernel re-checked, and the
    // theorem's recorded closure is the COMPOSED closure (its own ∪ both
    // carried definitions') — foundational-only across the whole chain.
    let mut env = Environment::new();
    env.add_decl(definition(PID_DEF, pid_type(), pid_value()))
        .expect("PId definition must kernel-check");
    env.add_decl(definition(PCOMP_DEF, pid_type(), pcomp_value()))
        .expect("PComp definition must kernel-check");
    env.add_decl(theorem(USES_PCOMP, uses_pcomp_type(), uses_pcomp_value()))
        .expect("uses_pcomp must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_PCOMP]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    assert_eq!(record.result.accepted, vec![USES_PCOMP.to_string()]);
    let thm = entry(&record, USES_PCOMP);
    assert!(thm.accepted, "uses_pcomp must graduate under v2");
    // Composed closure: theorem ∪ PComp ∪ PId — all foundational-only.
    assert!(thm.axiom_closure.foundational_only);
    assert!(thm.axiom_closure.domain_axioms.is_empty());
    assert_eq!(
        thm.carried_definitions,
        vec![PCOMP_DEF.to_string(), PID_DEF.to_string()],
        "the theorem's entry must record its full carried-definition closure"
    );

    // Record section: chain in dependency (shard) order, both required by
    // the accepted theorem, both with foundational-only contributions.
    assert_eq!(record.carried_definitions.len(), 2);
    assert_eq!(record.carried_definitions[0].name, PID_DEF);
    assert_eq!(record.carried_definitions[1].name, PCOMP_DEF);
    for def in &record.carried_definitions {
        assert_eq!(def.kernel.verdict, KernelVerdict::KernelVerified);
        assert!(def.kernel.value_typechecked);
        assert!(def.axiom_closure.foundational_only, "def {}", def.name);
        assert_eq!(def.required_by, vec![USES_PCOMP.to_string()]);
    }

    // Shard order: PId < PComp < theorem (each definition precedes its user).
    let shard_path = out.join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read graduated shard");
    assert_eq!(reader.header.constant_count, 3);
    let idx = |name: &str| {
        reader
            .lookup_name(name)
            .unwrap_or_else(|| panic!("{name} must be in the shard"))
            .0
    };
    assert!(idx(PID_DEF) < idx(PCOMP_DEF));
    assert!(idx(PCOMP_DEF) < idx(USES_PCOMP));

    // The cake gate replays the whole chain in order and re-earns it all.
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "chain-carrying shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    assert_eq!(report.checked, 3);
}

#[test]
fn test_graduate_v2_carried_definition_lean_order_caseson_recheck() {
    // Regression for the GRADUATION #3 blocker (List.concat.match_1 /
    // Int.neg.match_1): a carried definition whose VALUE applies a
    // prelude inductive's `casesOn` in Lean's argument order — motive,
    // MAJOR premise, then minors — must pass the gate's kernel re-check
    // against the `with_prelude` recheck environment. Before the
    // `build_cases_on` layout fix, Clean generated casesOn with the rec
    // layout (minors before the major), so every `.olean`-elaborated
    // match auxiliary mis-typechecked here: the major landed in the
    // first minor slot ("expected (fun x => motive x) [], got List α").
    //
    // `boolToProp b := @Bool.casesOn (fun _ => Prop) b True False`
    // exercises both the re-check (the application must match the
    // prelude casesOn's telescope) and iota reduction in the new order
    // (the theorem's type `boolToProp false` must reduce to `True`).
    const BOOL_CASE_DEF: &str = "GradPilot.boolToProp";
    const USES_BOOL_CASE: &str = "GradPilot.uses_bool_case";

    let bool_ty = Expr::const_str("Bool");
    let def_type = Expr::pi(bd(), bool_ty.clone(), Expr::prop());
    let def_value = {
        // fun (b : Bool) => @Bool.casesOn.{1} (fun _ => Prop) b True False
        let cases_on = Expr::const_(
            Name::from_string("Bool.casesOn"),
            vec![Level::succ(Level::zero())],
        );
        let motive = Expr::lam(bd(), bool_ty.clone(), Expr::prop());
        let body = Expr::app(
            Expr::app(
                Expr::app(Expr::app(cases_on, motive), Expr::bvar(0)),
                Expr::const_str("True"),
            ),
            Expr::const_str("False"),
        );
        Expr::lam(bd(), bool_ty.clone(), body)
    };
    // uses_bool_case : boolToProp Bool.false := True.intro
    // (well-typed only if the kernel iota-reduces the Lean-order casesOn).
    let thm_type = Expr::app(
        Expr::const_str(BOOL_CASE_DEF),
        Expr::const_str("Bool.false"),
    );
    let thm_value = Expr::const_str("True.intro");

    let mut env = Environment::with_prelude();
    env.add_decl(definition(BOOL_CASE_DEF, def_type, def_value))
        .expect("Lean-order casesOn definition must kernel-check in the source env");
    env.add_decl(theorem(USES_BOOL_CASE, thm_type, thm_value))
        .expect("uses_bool_case must kernel-check in the source env");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_BOOL_CASE]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    assert_eq!(
        record.result.accepted,
        vec![USES_BOOL_CASE.to_string()],
        "Lean-order casesOn user must graduate; rejections: {:?}",
        record
            .theorems
            .iter()
            .filter(|t| !t.accepted)
            .map(|t| (t.name.clone(), t.reject_reason.clone()))
            .collect::<Vec<_>>()
    );
    let thm = entry(&record, USES_BOOL_CASE);
    assert!(thm.accepted);
    assert!(thm.axiom_closure.foundational_only);
    assert_eq!(thm.carried_definitions, vec![BOOL_CASE_DEF.to_string()]);
    let def = &record.carried_definitions[0];
    assert_eq!(def.name, BOOL_CASE_DEF);
    assert_eq!(def.kernel.verdict, KernelVerdict::KernelVerified);
    assert!(def.kernel.value_typechecked);
}

#[test]
fn test_graduate_v2_definition_kernel_check_failure_cascades() {
    // A definition whose stored value does NOT kernel-check (injected via the
    // test-only structural path) must kill every dependent — first by a fresh
    // kernel re-check failure, then via the cached failure — and the shard
    // must carry nothing.
    const BOGUS_DEF: &str = "GradPilot.bogus_def";
    const USER_ONE: &str = "GradPilot.cites_bogus_one";
    const USER_TWO: &str = "GradPilot.cites_bogus_two";

    let mut env = Environment::new();
    env.add_decl_structural(definition(
        BOGUS_DEF,
        pid_type(),
        Expr::prop(), // Prop : Type — not a value of `Prop → Prop`
    ))
    .expect("structural bogus-definition fixture");
    // Proofs of `∀ p, p → p` that discard a `bogus_def` argument, so the
    // definition is referenced without affecting the statement. Added
    // structurally because the bogus def only "exists" structurally.
    let cites_bogus = |name: &str| {
        theorem(
            name,
            imp_self_type(),
            Expr::app(
                Expr::lam(bd(), pid_type(), imp_self_value()),
                Expr::const_str(BOGUS_DEF),
            ),
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
    assert!(record.carried_definitions.is_empty());
    let one = entry(&record, USER_ONE);
    assert!(!one.accepted);
    assert_eq!(one.kernel.verdict, KernelVerdict::Rejected);
    assert!(
        one.reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("carried-definition-failed")
                && r.contains(BOGUS_DEF)
                && r.contains("kernel")),
        "first dependent must fail on the definition's kernel re-check: {:?}",
        one.reject_reason
    );
    let two = entry(&record, USER_TWO);
    assert!(!two.accepted);
    assert!(
        two.reject_reason.as_deref().is_some_and(
            |r| r.starts_with("carried-definition-failed") && r.contains("already failed")
        ),
        "second dependent must fail via the cached definition failure: {:?}",
        two.reject_reason
    );

    // Shard is empty (and carries no definitions).
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_graduate_v2_rejects_cyclic_definition_dependencies() {
    // Carried-definition resolution is a topological walk; a reference cycle
    // among definitions has no dependency order, so it must be REJECTED with
    // an audited `dependency-cycle` reason — never looped on, never carried.
    // Cycles cannot pass the checked kernel path, so the fixture injects
    // them with the structural (test-only) path: a 2-cycle and a self-cycle.
    const CYC_A: &str = "GradPilot.cyc_a";
    const CYC_B: &str = "GradPilot.cyc_b";
    const SELF_REF: &str = "GradPilot.self_ref";
    const CITES_CYCLE: &str = "GradPilot.cites_cycle";
    const CITES_SELF: &str = "GradPilot.cites_self";

    let mut env = Environment::new();
    env.add_decl_structural(definition(CYC_A, Expr::prop(), Expr::const_str(CYC_B)))
        .expect("structural cycle fixture a");
    env.add_decl_structural(definition(CYC_B, Expr::prop(), Expr::const_str(CYC_A)))
        .expect("structural cycle fixture b");
    env.add_decl_structural(definition(
        SELF_REF,
        Expr::prop(),
        Expr::const_str(SELF_REF),
    ))
    .expect("structural self-cycle fixture");
    // Proofs of `∀ p, p → p` that discard a cyclic-definition argument.
    let cites = |name: &str, target: &str| {
        theorem(
            name,
            imp_self_type(),
            Expr::app(
                Expr::lam(bd(), Expr::prop(), imp_self_value()),
                Expr::const_str(target),
            ),
        )
    };
    env.add_decl_structural(cites(CITES_CYCLE, CYC_A))
        .expect("structural dependent of the 2-cycle");
    env.add_decl_structural(cites(CITES_SELF, SELF_REF))
        .expect("structural dependent of the self-cycle");

    let tmp = tempfile::tempdir().expect("tempdir");
    let record = graduate(
        &env,
        &names(&[CITES_CYCLE, CITES_SELF]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        tmp.path(),
    )
    .expect("graduation runs");

    assert!(record.result.accepted.is_empty());
    assert!(record.carried_definitions.is_empty());
    let two_cycle = entry(&record, CITES_CYCLE);
    assert!(!two_cycle.accepted);
    assert!(
        two_cycle
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("dependency-cycle")
                && r.contains(CYC_A)
                && r.contains(CYC_B)),
        "2-cycle must be rejected with both participants audited: {:?}",
        two_cycle.reject_reason
    );
    let self_cycle = entry(&record, CITES_SELF);
    assert!(!self_cycle.accepted);
    assert!(
        self_cycle
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("dependency-cycle") && r.contains(SELF_REF)),
        "self-cycle must be rejected with the participant audited: {:?}",
        self_cycle.reject_reason
    );

    // Nothing reaches the shard.
    let shard_path = tmp.path().join(&record.result.shard_filename);
    let reader = ShardReader::from_file(&shard_path).expect("read shard");
    assert_eq!(reader.header.constant_count, 0);
}

// ---------------------------------------------------------------------------
// v2 conversion re-run: the GRADUATION #1 environment
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_v2_native_env_converts_definition_blocked_rejections() {
    // GRADUATION #1 (v1 gate, this same environment): 109 accepted / 168
    // rejected, of which 72 `external-dependency` (all definition-valued
    // dependencies) and 96 `rejected-dependency` cascades. v2 carries
    // definitions, so the definition-blocked set must convert: no rejection
    // may cite a definition as external, and the accepted count must
    // strictly dominate the v1 run's 109.
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
    let total = candidates.len();

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &candidates,
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    // No definition-valued dependency may be rejected as external anymore.
    for thm in &record.theorems {
        if let Some(reason) = thm.reject_reason.as_deref() {
            assert!(
                !(reason.starts_with("external-dependency") && reason.contains("(definition)")),
                "v2 must carry definition dependencies; {} still rejected with: {reason}",
                thm.name
            );
        }
    }

    let accepted = record.result.accepted.len();
    assert_eq!(total, accepted + record.result.rejected.len());
    assert!(
        accepted > 109,
        "v2 must strictly dominate GRADUATION #1's 109 accepted; got {accepted}/{total}"
    );
    assert!(
        !record.carried_definitions.is_empty(),
        "the native environment's NNVerify/Rat content must carry definitions"
    );

    // Every carried definition re-checked, foundational-only, and required.
    for def in &record.carried_definitions {
        assert_eq!(def.kernel.verdict, KernelVerdict::KernelVerified);
        assert!(def.kernel.value_typechecked);
        assert!(def.axiom_closure.foundational_only, "def {}", def.name);
        assert!(!def.required_by.is_empty(), "def {}", def.name);
    }

    // The produced shard passes the unbypassable cake gate, definitions
    // replayed in dependency order before their users.
    let shard_path = out.join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "native v2 shard must pass the cake gate; violations: {:?}",
        report.violations
    );
    // v3: the shard additionally carries inductive-family member constants
    // for the formerly value-less carriers (see the v3 conversion twin);
    // v3.1 adds carried theorems (duplicate-rejected candidates required by
    // accepted dependents enter the shard as supporting material).
    let family_member_count: usize = record
        .carried_inductives
        .iter()
        .map(|f| f.members_in_shard.len())
        .sum();
    assert_eq!(
        report.checked,
        accepted
            + record.carried_definitions.len()
            + record.carried_theorems.len()
            + family_member_count
    );

    // Conversion telemetry for the GRADUATION #2 report (visible with
    // `--nocapture`).
    let mut reasons: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for thm in &record.theorems {
        let key = thm
            .reject_reason
            .as_deref()
            .map_or("ACCEPTED", |r| r.split(':').next().unwrap_or(r));
        *reasons.entry(key).or_default() += 1;
    }
    println!(
        "v2 native re-run: accepted {accepted}/{total}, carried {} definitions",
        record.carried_definitions.len()
    );
    for (reason, count) in reasons {
        println!("  {count:4}  {reason}");
    }
    for def in &record.carried_definitions {
        println!(
            "  CARRIED {} (required_by {} theorems)",
            def.name,
            def.required_by.len()
        );
    }
    let converted: Vec<&str> = record
        .theorems
        .iter()
        .filter(|t| t.accepted && !t.carried_definitions.is_empty())
        .map(|t| t.name.as_str())
        .collect();
    println!(
        "  CONVERTED {} theorems accepted only via carried definitions:",
        converted.len()
    );
    for name in converted {
        println!("    {name}");
    }
    for thm in &record.theorems {
        if let Some(reason) = thm.reject_reason.as_deref() {
            if reason.starts_with("external-dependency")
                || reason.starts_with("carried-definition-failed")
                || reason.starts_with("unknown-constant")
                || reason.starts_with("dependency-")
            {
                println!("  DETAIL {}: {}", thm.name, reason);
            }
        }
    }
}
