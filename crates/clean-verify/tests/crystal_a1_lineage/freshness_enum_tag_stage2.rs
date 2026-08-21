// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Current-source lineage and source-bound fixture-rebaseline gate.

use super::*;

fn assert_admitted_drift_class(stem: &str, class: &Value) {
    let class = class.as_str().unwrap_or("");
    assert!(
        matches!(
            class,
            "functy-index"
                | "type-table-index"
                | "callee-index"
                | "global-index"
                | "loc-file-index"
        ),
        "{stem}: {CURRENT_RECORD} contains unknown drift class `{class}`"
    );
}

/// The live dump binds every historical fixture pin to a current lineage and
/// records all five executable links, without rewriting the historical file.
#[test]
fn enum_tag_stage2_revalidation_covers_every_chain_and_all_links() {
    let record = read_json(CURRENT_RECORD);
    assert_eq!(
        record["schema"].as_str(),
        Some("clean.crystal.chain_revalidation/v3")
    );
    assert_eq!(
        record["provenance"]["clean_source_rev"].as_str(),
        Some("b03937e748123cc115bfd159694fd64f0ce8538a")
    );
    assert_eq!(
        record["supersedes_for_current_source_scope"].as_str(),
        Some("data/crystal_chain_revalidation_2026-08-20_a152ab39e.json")
    );
    assert_eq!(
        record["provenance"]["trust_worktree_rev"].as_str(),
        Some("8ea68367816ce49a7c3026f1e19c7ee4285e7737")
    );
    assert_eq!(
        record["provenance"]["trustc_sha256"].as_str(),
        Some("c4b91deb28f50697883de56664595a5afc86f8ec8af8de9d357b6757a7867e80")
    );
    assert_eq!(
        record["provenance"]["librustc_driver_sha256"].as_str(),
        Some("a2e495e3e4918964c071d18c420d24f69b781f55829ff63c72fdeaa904d9fce5")
    );
    assert_eq!(
        record["generator"]["script"].as_str(),
        Some("scripts/crystal_chain_revalidation.py")
    );
    assert_eq!(record["generator"]["append_only"].as_bool(), Some(true));
    assert_eq!(
        record["generator"]["fixture_rebaseline_record"].as_str(),
        Some(CURRENT_REBASELINE)
    );
    assert_eq!(
        record["generator"]["fixture_rebaseline_schema"].as_str(),
        Some("clean.crystal.fixture_rebaseline/v1")
    );

    let rebaseline = read_json(CURRENT_REBASELINE);
    let bindings = read_json(CURRENT_REBASELINE_BINDINGS);
    assert_eq!(
        rebaseline["schema"].as_str(),
        Some("clean.crystal.fixture_rebaseline/v1")
    );
    assert_eq!(rebaseline["append_only"].as_bool(), Some(true));
    assert_eq!(
        rebaseline["provenance"]["clean_source_rev"].as_str(),
        record["provenance"]["clean_source_rev"].as_str()
    );
    assert_eq!(
        bindings["schema"].as_str(),
        Some("clean.crystal.fixture_rebaseline_bindings/v1")
    );
    assert_eq!(
        bindings["clean_source_rev"].as_str(),
        record["provenance"]["clean_source_rev"].as_str()
    );
    assert_eq!(
        rebaseline["supersedes_for_current_source_scope"].as_str(),
        Some("data/crystal_fixture_rebaseline_2026-08-20_a152ab39e.json")
    );
    assert_eq!(
        bindings["binding_mode"].as_str(),
        Some("identical-fixtures-successor")
    );
    assert_eq!(
        bindings["prior_rebaseline_record"].as_str(),
        rebaseline["supersedes_for_current_source_scope"].as_str()
    );
    assert_eq!(
        bindings["prior_binding_manifest"].as_str(),
        Some("data/crystal_fixture_rebaseline_bindings_2026-08-20_a152ab39e.json")
    );
    assert!(
        bindings["bindings"].as_array().is_some_and(Vec::is_empty),
        "byte-identical fixtures inherit the authenticated predecessor bindings; a new numeric \
         delta here would require an explicit proof/spec/tag re-pin"
    );
    for predecessor in [
        bindings["prior_rebaseline_record"].as_str().unwrap_or(""),
        bindings["prior_binding_manifest"].as_str().unwrap_or(""),
    ] {
        assert!(
            repo_root().join(predecessor).is_file(),
            "the current successor names missing append-only predecessor {predecessor}"
        );
    }
    let binary_sha = rebaseline["provenance"]["dump_binary_sha256"]
        .as_str()
        .expect("the rebaseline must bind the binary TrustIR artifact");
    assert_eq!(
        bindings["dump_bin_sha256"].as_str(),
        Some(binary_sha),
        "the reviewed binding manifest names another binary artifact"
    );
    assert_eq!(
        record["artifacts"]["clean_kernel.trust-ir.bin"]["sha256"].as_str(),
        Some(binary_sha),
        "the chain record and fixture rebaseline name different binary artifacts"
    );
    let measurement_driver = record["provenance"]["measurement_driver"]
        .as_str()
        .expect("the chain record must name the source of its live-build recipe");
    assert_eq!(
        rebaseline["provenance"]["measurement_driver"].as_str(),
        Some(measurement_driver),
        "the chain and rebaseline records name different measurement drivers"
    );
    let expected_driver_sha = record["provenance"]["measurement_driver_sha256"]
        .as_str()
        .expect("the chain record must hash its measurement driver");
    assert_eq!(
        rebaseline["provenance"]["measurement_driver_sha256"].as_str(),
        Some(expected_driver_sha),
        "the chain and rebaseline records hash different measurement drivers"
    );
    let driver_path = repo_root().join(measurement_driver);
    let hash = std::process::Command::new("python3")
        .args([
            "-c",
            "import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],'rb').read()).hexdigest())",
        ])
        .arg(&driver_path)
        .output()
        .unwrap_or_else(|e| {
            panic!(
                "could not hash {} with python3 ({e})",
                driver_path.display()
            )
        });
    assert!(
        hash.status.success(),
        "could not hash {}: {}",
        driver_path.display(),
        String::from_utf8_lossy(&hash.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&hash.stdout).trim(),
        expected_driver_sha,
        "the committed measurement driver moved after the live dump was taken"
    );

    let invariants = record["fatal_invariants"]
        .as_object()
        .expect("the current record must carry fatal_invariants");
    assert!(!invariants.is_empty());
    for (name, value) in invariants {
        assert_eq!(
            value.as_u64(),
            Some(0),
            "{CURRENT_RECORD}: fatal invariant {name} is non-zero"
        );
    }

    let chains = record["chains"]
        .as_object()
        .expect("the current record must carry a chains object");
    assert_eq!(
        chains.len(),
        EVIDENCE.len(),
        "the current revalidation must cover every chain, including HEAD_MEASURED rows"
    );

    for (stem, file) in EVIDENCE {
        let entry = chains
            .get(*stem)
            .unwrap_or_else(|| panic!("{CURRENT_RECORD} carries no entry for {stem}"));
        let fixture = evidence(file);
        let current = fixture["current_source_bound_pin"]
            .as_object()
            .unwrap_or_else(|| {
                panic!(
                    "{file}: current fixture text was source-bound to the Clean-0.4 dump, but the evidence has no \
                 complete current_source_bound_pin"
            )
            });
        assert_eq!(
            current.get("schema").and_then(Value::as_str),
            Some("clean.crystal.current_source_bound_pin/v1")
        );
        assert_eq!(
            current.get("record").and_then(Value::as_str),
            Some(CURRENT_REBASELINE)
        );
        assert_eq!(
            current.get("binding_manifest").and_then(Value::as_str),
            Some(CURRENT_REBASELINE_BINDINGS)
        );
        assert_eq!(
            current["build"]["artifacts"]["clean_kernel.trust-ir.bin"]["sha256"].as_str(),
            Some(binary_sha),
            "{stem}: the current pin is not bound to the exact binary used by reader A"
        );
        let body = &entry["emitted_body_vs_committed_fixture"];
        let links = &entry["links_at_head"];
        let lineage = &entry["lineage"];

        assert_eq!(
            lineage["pinned_in_fixture"].as_str(),
            current.get("lineage").and_then(Value::as_str),
            "{stem}: the current record is not bound to the current source-bound lineage"
        );
        assert_eq!(
            lineage["pinned_def_index"].as_u64(),
            current.get("def_index").and_then(Value::as_u64),
            "{stem}: the current record is not bound to the current def_index"
        );
        assert_eq!(
            links["instr_count"].as_u64(),
            current.get("instr_count").and_then(Value::as_u64),
            "{stem}: instruction count moved"
        );
        assert_eq!(body["verdict"].as_str(), Some("IDENTICAL"));
        assert_eq!(
            body["drift_classes"].as_array().map(Vec::is_empty),
            Some(true)
        );
        assert_eq!(body["instructions_moved"].as_u64(), Some(0));
        for class in body["drift_classes"].as_array().unwrap_or(&Vec::new()) {
            assert_admitted_drift_class(stem, class);
        }

        assert_eq!(
            links["lowered"].as_bool(),
            Some(true),
            "{stem}: not lowered"
        );
        assert_eq!(
            links["spliced"].as_bool(),
            Some(true),
            "{stem}: not spliced"
        );
        assert_eq!(
            links["unsupported"].as_array().map(Vec::is_empty),
            Some(true),
            "{stem}: live dump reports unsupported lowering"
        );
        assert_eq!(
            links["derived_mir"]["verdict"].as_str(),
            Some("agreed"),
            "{stem}: derived MIR did not agree"
        );
        assert_eq!(
            links["derived_mir"]["markers_exact"].as_bool(),
            Some(true),
            "{stem}: marker channel is not exact"
        );
        assert_eq!(
            links["flip_fired"].as_bool(),
            Some(true),
            "{stem}: codegen flip did not fire"
        );

        let current = lineage["at_head"].as_str().unwrap_or("");
        assert!(
            current.starts_with("sha256:") && current.len() > "sha256:".len(),
            "{stem}: current lineage is not a sha256 identity"
        );
        assert_eq!(
            lineage["moved"].as_bool(),
            Some(lineage["pinned_in_fixture"].as_str() != Some(current)),
            "{stem}: the record's moved flag disagrees with its two lineage identities"
        );
    }
}

/// The helper fixture is compared too, but it is not promoted into a chain:
/// its derived-MIR lane remains unsupported and it does not flip.
#[test]
fn enum_tag_stage2_revalidation_keeps_the_deref_helper_fail_closed() {
    let record = read_json(CURRENT_RECORD);
    let helper = &record["extra_fixtures"]["level_is_zero_deref_callee"];
    assert_eq!(
        helper["emitted_body_vs_committed_fixture"]["verdict"].as_str(),
        Some("IDENTICAL"),
        "the helper must be byte-identical under strict current-source freshness"
    );
    assert_eq!(
        helper["emitted_body_vs_committed_fixture"]["drift_classes"]
            .as_array()
            .map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(
        helper["emitted_body_vs_committed_fixture"]["instructions_moved"].as_u64(),
        Some(0)
    );
    assert_eq!(
        helper["links_at_head"]["derived_mir"]["verdict"].as_str(),
        Some("unsupported")
    );
    assert_eq!(helper["links_at_head"]["flip_fired"].as_bool(), Some(false));
}

/// The current pins cover every chain exactly once, retain every historical
/// top-level identity, and agree with the append-only old->new ledger.
#[test]
fn source_bound_pins_are_one_to_one_and_history_remains_queryable() {
    let ledger = read_json(CURRENT_REBASELINE);
    let evidence_rows = ledger["lineage_evidence"]
        .as_object()
        .expect("the rebaseline ledger must carry lineage_evidence");
    assert_eq!(evidence_rows.len(), EVIDENCE.len());
    assert_eq!(
        ledger["primary_body_count"].as_u64(),
        Some(EVIDENCE.len() as u64)
    );
    assert_eq!(ledger["helper_body_count"].as_u64(), Some(1));

    let mut seen_records = BTreeSet::new();
    for (stem, file) in EVIDENCE {
        let historical = evidence(file);
        let current = &historical["current_source_bound_pin"];
        let row = evidence_rows
            .get(*stem)
            .unwrap_or_else(|| panic!("{CURRENT_REBASELINE} has no lineage row for {stem}"));
        assert!(
            historical["lineage"].as_str().is_some(),
            "{file}: historical top-level lineage was erased"
        );
        assert_eq!(
            row["historical_top_level_lineage"].as_str(),
            historical["lineage"].as_str(),
            "{stem}: ledger no longer preserves the historical identity"
        );
        assert_eq!(
            row["current_lineage"].as_str(),
            current["lineage"].as_str(),
            "{stem}: ledger/current pin disagree"
        );
        seen_records.insert(current["record"].as_str().unwrap_or("").to_owned());
    }
    assert_eq!(
        seen_records,
        BTreeSet::from([CURRENT_REBASELINE.to_owned()])
    );
}

/// Cheap mutation controls run in the ordinary Rust gate so the rebaseline
/// writer cannot silently lose its stale-source, missing-row, duplicate-body,
/// or falsified-report refusals.
#[test]
fn source_bound_rebaseline_fail_closed_controls_pass() {
    let root = repo_root();
    let output = std::process::Command::new("python3")
        .arg(root.join("scripts/crystal_fixture_rebaseline.py"))
        .arg("--selftest")
        .current_dir(&root)
        .output()
        .expect("python3 must run the source-bound rebaseline controls");
    assert!(
        output.status.success(),
        "rebaseline controls failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("5 fail-closed controls"),
        "the selftest exited without running the complete control set"
    );
}
