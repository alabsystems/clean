// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v3 conversion re-run: the GRADUATION #2 environment (the measurement twin
// of design §7 — value-less carriers must stop blocking).

#[test]
fn test_graduate_v3_native_env_converts_inductive_blocked_rejections() {
    // GRADUATION #2 (v2 gate, this same environment): 125 accepted / 156
    // rejected — 70 `external-dependency` on the two value-less carriers
    // (`Rat.Raw` ×42, `NNVerify.IntervalBounds` ×28) and 86
    // `rejected-dependency` cascades, ALL tracing to those two families
    // (design §7: zero residue). v3 carries inductive families, so the
    // blocked set must convert: no rejection may cite a definition OR an
    // inductive as an unresolvable external/value-less dependency, and the
    // accepted count must strictly dominate the v2 run's 125.
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

    // The v3 conversion bar (design §7): zero rejections naming a
    // definition or inductive-family member as an uncarryable dependency.
    for thm in &record.theorems {
        if let Some(reason) = thm.reject_reason.as_deref() {
            assert!(
                !reason.starts_with("external-dependency"),
                "v3 must carry definition AND inductive dependencies; {} still \
                 rejected with: {reason}",
                thm.name
            );
            assert!(
                !reason.starts_with("carried-inductive"),
                "no native-env family may fail its v3 carry; {} rejected with: {reason}",
                thm.name
            );
        }
    }

    let accepted = record.result.accepted.len();
    assert_eq!(total, accepted + record.result.rejected.len());
    assert!(
        accepted > 125,
        "v3 must strictly dominate GRADUATION #2's 125 accepted; got {accepted}/{total}"
    );
    assert!(
        !record.carried_inductives.is_empty(),
        "the native environment's value-less carriers must be carried as families"
    );
    let family_names: Vec<&str> = record
        .carried_inductives
        .iter()
        .map(|f| f.name.as_str())
        .collect();
    assert!(
        family_names.contains(&"Rat.Raw"),
        "Rat.Raw (42 direct v2 rejections) must be carried: {family_names:?}"
    );
    assert!(
        family_names.contains(&"NNVerify.IntervalBounds"),
        "NNVerify.IntervalBounds (28 direct v2 rejections) must be carried: {family_names:?}"
    );

    // Every carried family re-checked, family-checked, foundational-only,
    // and required; every carried definition unchanged from v2 discipline.
    for fam in &record.carried_inductives {
        assert_eq!(fam.kernel.verdict, KernelVerdict::KernelVerified);
        assert!(fam.kernel.family_checked, "family {}", fam.name);
        assert!(!fam.kernel.value_typechecked, "family {}", fam.name);
        assert!(fam.axiom_closure.foundational_only, "family {}", fam.name);
        assert!(!fam.required_by.is_empty(), "family {}", fam.name);
    }
    for def in &record.carried_definitions {
        assert_eq!(def.kernel.verdict, KernelVerdict::KernelVerified);
        assert!(def.kernel.value_typechecked);
        assert!(def.axiom_closure.foundational_only, "def {}", def.name);
        assert!(!def.required_by.is_empty(), "def {}", def.name);
    }

    // The produced shard passes the unbypassable cake gate, families and
    // definitions replayed in dependency order before their users.
    let shard_path = out.join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "native v3 shard must pass the cake gate; violations: {:?}",
        report.violations
    );
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
    // v3.1: every carried theorem in this run is a duplicate-rejected
    // candidate required by an accepted dependent — kernel-verified,
    // foundational-only, honest duplicate novelty.
    for thm in &record.carried_theorems {
        assert_eq!(
            thm.kernel.verdict,
            KernelVerdict::KernelVerified,
            "{}",
            thm.name
        );
        assert!(thm.kernel.value_typechecked, "{}", thm.name);
        assert!(thm.axiom_closure.foundational_only, "{}", thm.name);
        assert!(!thm.required_by.is_empty(), "{}", thm.name);
        assert_eq!(
            thm.novelty.verdict,
            NoveltyVerdict::Duplicate,
            "native carried theorems arise from duplicate-policy rejections: {}",
            thm.name
        );
    }

    // Conversion telemetry for the GRADUATION #3 report (visible with
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
        "v3 native re-run: accepted {accepted}/{total}, carried {} definitions + {} families \
         ({} family members in shard)",
        record.carried_definitions.len(),
        record.carried_inductives.len(),
        family_member_count
    );
    for (reason, count) in reasons {
        println!("  {count:4}  {reason}");
    }
    for fam in &record.carried_inductives {
        println!(
            "  CARRIED FAMILY {} (required_by {} theorems; members: {})",
            fam.name,
            fam.required_by.len(),
            fam.members_in_shard
                .iter()
                .map(|m| m.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    let converted: Vec<&str> = record
        .theorems
        .iter()
        .filter(|t| t.accepted && !t.carried_inductives.is_empty())
        .map(|t| t.name.as_str())
        .collect();
    println!(
        "  CONVERTED {} accepted theorems close over carried families",
        converted.len()
    );
    for thm in &record.theorems {
        if let Some(reason) = thm.reject_reason.as_deref() {
            println!("  DETAIL {}: {}", thm.name, reason);
        }
    }
}
