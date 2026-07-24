// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test for the `proof_mechanism` schema + constructive-claim
//! gate introduced in #3435.
//!
//! This test loads `data/axiom_audit.json`, iterates every conjecture that
//! claims `proof_mechanism: "constructive"`, and runs the same transitive
//! axiom closure check that the `verify_constructive_claims` binary and
//! the `verify_axiom_audit` Python gate both perform. Every theorem in
//! the conjecture's namespace must have `env.axiom_deps()` return an empty
//! set (i.e. only FOUNDATIONAL_AXIOMS appear in the transitive closure).
//!
//! If no conjectures currently claim `constructive`, the test passes
//! deliberately with a short diagnostic. This is the expected state
//! immediately after schema migration (all conjectures start as
//! non-constructive/non-closure-gated proof mechanisms) and BEFORE the first
//! real constructive proof lands.
//!
//! Part of #3435.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

use clean_kernel::env::gamma_crown_verify::{init_conjecture, CONJECTURE_IDS};
use clean_kernel::{ConstantKind, Name};
use serde_json::Value;

/// Mirror of `verify_constructive_claims::conjecture_theorem_prefixes`.
/// Kept in sync manually: both are dispatched from the same authoritative
/// table in `gamma_crown_verify.rs`. A drift between the two would show up
/// as an empty theorem list here (and correspondingly a failing gate),
/// which is the failure mode we want anyway.
fn conjecture_theorem_prefixes(id: &str) -> &'static [&'static str] {
    match id {
        "C001" => &["NNVerify.C001."],
        "C002" => &["NNVerify.C002."],
        "C003" => &["NNVerify.ECLipsE.", "NNVerify.Lipschitz."],
        "C004" => &["NNVerify.C004."],
        "C005" => &["NNVerify.McCormick."],
        "C006" => &["NNVerify.C006."],
        "C007" => &["NNVerify.C007."],
        "C008" => &["NNVerify.ibp_tightness_"],
        "C009" => &[
            "NNVerification.ibp_wrapping_",
            "NNVerification.crown_",
            "NNVerification.norm_product_",
            "NNVerification.ratio_",
            "NNVerification.c009_",
            "NNVerification.C009",
        ],
        "C010" => &["NNVerify.C010.", "NNVerify.RobustnessGen."],
        "C011" => &["NNVerify.C011."],
        "C012" => &["NNVerify.C012."],
        "C028" => &["NNVerify.C028."],
        "C029" => &["NNVerify.PacProof."],
        "C030" => &["NNVerify.OrbitCROWN."],
        _ => &[],
    }
}

/// Resolve the repo root from CARGO_MANIFEST_DIR so we can find
/// `data/axiom_audit.json` regardless of where `cargo test` is run from.
fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR -> crates/clean-kernel
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest)
        .parent() // crates/
        .and_then(|p| p.parent()) // repo root
        .expect("resolve repo root from CARGO_MANIFEST_DIR")
        .to_path_buf()
}

fn load_audit_json() -> Value {
    let path = repo_root().join("data").join("axiom_audit.json");
    let raw = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {}", path.display(), e));
    serde_json::from_str(&raw)
        .unwrap_or_else(|e| panic!("failed to parse {}: {}", path.display(), e))
}

/// Load `data/soundness_tcb.json` — the soundness-certificate C2 golden, the
/// single source of truth for the kernel trusted-base axiom set. It is pinned
/// fail-closed to the LIVE cert by `golden_matches_live_axioms` (and is the
/// same file the kernel `include_str!`s at `soundness_certificate.rs:56`).
fn load_soundness_tcb_json() -> Value {
    let path = repo_root().join("data").join("soundness_tcb.json");
    let raw = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {}", path.display(), e));
    serde_json::from_str(&raw)
        .unwrap_or_else(|e| panic!("failed to parse {}: {}", path.display(), e))
}

/// FAIL-CLOSED cert↔audit consistency (exhaustive-audit follow-up, 2026-06-17).
///
/// The `soundness_tcb_mirror` block in `data/axiom_audit.json` MUST match
/// `data/soundness_tcb.json` (the soundness-certificate C2 golden) exactly.
/// The golden is itself pinned to the LIVE cert by `golden_matches_live_axioms`,
/// so this transitively binds the project's first-class trusted-base
/// domain-axiom metric to the certificate — and blocks the silent drift that
/// previously let the headline read `total_domain_axioms=2` while the real
/// kernel TCB carried 9 domain axioms (stale by 779 commits).
///
/// Wired into `just gate` (scripts/local_gate.sh). Read-only by design: it
/// asserts equality and never rewrites the file (a mutating gate would hide
/// drift rather than surface it).
#[test]
fn axiom_audit_tcb_mirror_matches_soundness_tcb_golden() {
    let audit = load_audit_json();
    let golden = load_soundness_tcb_json();

    let mirror = audit
        .get("soundness_tcb_mirror")
        .and_then(|v| v.as_object())
        .expect(
            "data/axiom_audit.json: 'soundness_tcb_mirror' block missing — it must mirror \
             data/soundness_tcb.json (the cert C2 golden). See \
             verify_axiom_audit_integration.rs::axiom_audit_tcb_mirror_matches_soundness_tcb_golden.",
        );

    let golden_i64 = |key: &str| -> i64 {
        golden
            .get(key)
            .and_then(|v| v.as_i64())
            .unwrap_or_else(|| panic!("data/soundness_tcb.json: {key} must be a non-null integer"))
    };
    let mirror_i64 = |key: &str| -> i64 {
        mirror
            .get(key)
            .and_then(|v| v.as_i64())
            .unwrap_or_else(|| panic!("soundness_tcb_mirror.{key} must be a non-null integer"))
    };

    // (1) The four scalar TCB counts must match the golden verbatim.
    for key in [
        "axiom_count",
        "foundational_count",
        "admitted_domain_count",
        "other_admitted_count",
    ] {
        let (m, g) = (mirror_i64(key), golden_i64(key));
        assert_eq!(
            m, g,
            "data/axiom_audit.json drifted from data/soundness_tcb.json (cert C2 golden): \
             soundness_tcb_mirror.{key}={m} != {g}. Regenerate the golden via \
             `REGEN_SOUNDNESS_GOLDEN=1 cargo test -p clean-kernel --lib --features math-overlays \
             golden_matches_live_axioms`, then sync the soundness_tcb_mirror block in \
             data/axiom_audit.json.",
        );
    }

    // (2) domain_axiom_count == admitted_domain_count + other_admitted_count.
    let expected_domain = golden_i64("admitted_domain_count") + golden_i64("other_admitted_count");
    let domain_count = mirror_i64("domain_axiom_count");
    assert_eq!(
        domain_count, expected_domain,
        "soundness_tcb_mirror.domain_axiom_count={domain_count} != \
         admitted_domain_count+other_admitted_count={expected_domain}.",
    );

    // (3) The mirror's (foundational ∪ domain) axiom NAMES must equal the
    //     golden's flat `axioms` list exactly — no missing or extra names.
    let golden_axioms: BTreeSet<String> = golden
        .get("axioms")
        .and_then(|v| v.as_array())
        .expect("data/soundness_tcb.json: 'axioms' must be an array")
        .iter()
        .map(|v| {
            v.as_str()
                .expect("soundness_tcb.json axiom name must be a string")
                .to_string()
        })
        .collect();
    let mirror_names = |key: &str| -> BTreeSet<String> {
        mirror
            .get(key)
            .and_then(|v| v.as_array())
            .unwrap_or_else(|| panic!("soundness_tcb_mirror.{key} must be an array"))
            .iter()
            .map(|v| {
                v.as_str()
                    .expect("soundness_tcb_mirror axiom name must be a string")
                    .to_string()
            })
            .collect()
    };
    let mut mirror_all = mirror_names("foundational_axioms");
    let domain_names = mirror_names("domain_axioms");
    mirror_all.extend(domain_names.iter().cloned());
    assert_eq!(
        mirror_all, golden_axioms,
        "data/axiom_audit.json drifted from data/soundness_tcb.json: \
         soundness_tcb_mirror.(foundational_axioms ∪ domain_axioms) != soundness_tcb.json axioms. \
         Sync the soundness_tcb_mirror block from the golden.",
    );

    // (4) domain_axioms name count is consistent with domain_axiom_count.
    assert_eq!(
        domain_names.len() as i64,
        domain_count,
        "soundness_tcb_mirror.domain_axioms lists {} names but domain_axiom_count={domain_count}.",
        domain_names.len(),
    );
}

#[test]
fn axiom_audit_has_proof_mechanism_for_every_conjecture() {
    let audit = load_audit_json();
    let conjectures = audit
        .get("conjectures")
        .and_then(|v| v.as_object())
        .expect("axiom_audit.json: 'conjectures' must be an object");

    let mut missing: Vec<String> = Vec::new();
    for cid in CONJECTURE_IDS {
        let entry = match conjectures.get(*cid) {
            Some(e) => e,
            None => {
                missing.push(format!("{cid}: entry missing"));
                continue;
            }
        };
        match entry.get("proof_mechanism") {
            Some(Value::String(mech)) => {
                assert!(
                    matches!(
                        mech.as_str(),
                        "constructive"
                            | "sorry_inhabited"
                            | "axiom_wrapper"
                            | "unchecked"
                            | "mixed"
                            | "masquerade_demoted"
                            | "hypothesis_wrapped"
                            | "hypothesis_wrapped_local_evidence"
                    ),
                    "{cid}: unknown proof_mechanism value '{mech}'",
                );
            }
            _ => missing.push(format!("{cid}: proof_mechanism missing or not a string")),
        }
    }
    assert!(
        missing.is_empty(),
        "axiom_audit.json schema violations:\n  {}",
        missing.join("\n  "),
    );
}

/// Collect conjecture IDs whose `proof_mechanism` is the literal string
/// `"constructive"`. Returns empty vec when the schema has no claimants.
fn collect_constructive_claimants(conjectures: &serde_json::Map<String, Value>) -> Vec<String> {
    conjectures
        .iter()
        .filter_map(|(cid, entry)| match entry.get("proof_mechanism") {
            Some(Value::String(m)) if m == "constructive" => Some(cid.clone()),
            _ => None,
        })
        .collect()
}

/// Audit all theorems in one claimed-constructive conjecture. Returns the
/// list of (theorem_name, sorted_closure_names) pairs that have non-empty
/// transitive axiom closures — i.e. the failures for this conjecture.
fn audit_one_conjecture(cid: &str) -> Vec<(String, Vec<String>)> {
    let env = init_conjecture(cid).unwrap_or_else(|e| panic!("init_conjecture({cid}) failed: {e}"));

    let prefixes = conjecture_theorem_prefixes(cid);
    let theorem_names: Vec<Name> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Theorem)
        .filter(|c| {
            let s = c.name.to_string();
            prefixes.iter().any(|p| s.starts_with(p))
        })
        .map(|c| c.name.clone())
        .collect();

    assert!(
        !theorem_names.is_empty(),
        "{cid}: claimed 'constructive' but no theorems registered under {prefixes:?}",
    );

    let mut failures: Vec<(String, Vec<String>)> = Vec::new();
    for name in &theorem_names {
        let deps = env
            .axiom_deps(name)
            .unwrap_or_else(|| panic!("axiom_deps({name}) returned None"));
        if !deps.is_empty() {
            let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            dep_strs.sort();
            failures.push((name.to_string(), dep_strs));
        }
    }
    failures
}

fn format_failures(failures: &BTreeMap<String, Vec<(String, Vec<String>)>>) -> String {
    failures
        .iter()
        .map(|(cid, rows)| {
            let body: String = rows
                .iter()
                .map(|(thm, deps)| format!("    {thm} -> {deps:?}"))
                .collect::<Vec<_>>()
                .join("\n");
            format!("  {cid}:\n{body}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn every_constructive_claim_has_empty_transitive_axiom_closure() {
    let audit = load_audit_json();
    let conjectures = audit
        .get("conjectures")
        .and_then(|v| v.as_object())
        .expect("axiom_audit.json: 'conjectures' must be an object");

    let claimed = collect_constructive_claimants(conjectures);
    if claimed.is_empty() {
        // Deliberate: the schema migration lands all conjectures as
        // non-constructive/non-closure-gated mechanisms. Until a genuine
        // constructive proof is wired in, there is nothing to gate.
        // This is a pass, not a vacuous skip.
        eprintln!(
            "[verify_axiom_audit] no conjectures currently claim \
             `proof_mechanism: constructive` — gate passes with nothing to check.",
        );
        return;
    }

    let mut failures: BTreeMap<String, Vec<(String, Vec<String>)>> = BTreeMap::new();
    for cid in &claimed {
        let rows = audit_one_conjecture(cid);
        if !rows.is_empty() {
            failures.insert(cid.clone(), rows);
        }
    }

    assert!(
        failures.is_empty(),
        "constructive claims failed transitive-axiom-closure check:\n{}",
        format_failures(&failures),
    );
}

// ---------------------------------------------------------------------------
// #3641 — per-conjecture vs top-level reconciliation anchor tests
// ---------------------------------------------------------------------------

/// Sum `axioms` across all conjectures, accepting both scalar-int and
/// historical list-shaped representations (mirrors
/// `recompute_axiom_audit_aggregates._as_int_count`).
fn sum_conjecture_field(conjectures: &serde_json::Map<String, Value>, field: &str) -> i64 {
    let mut total: i64 = 0;
    for (_cid, entry) in conjectures {
        let val = entry.get(field).unwrap_or(&Value::Null);
        let n: i64 = match val {
            Value::Number(n) => n.as_i64().expect("axioms/theorems field must be integer"),
            Value::Array(a) => a.len() as i64,
            Value::Null => 0,
            other => panic!("{field}: unexpected type {other:?}"),
        };
        total += n;
    }
    total
}

/// Sum `non_conjecture_axioms.per_prefix.*.count` (returns 0 when the block
/// is absent). Mirrors `compute_non_conjecture_axiom_total` in
/// `scripts/axiom_audit/aggregates.py`.
fn sum_non_conjecture_axioms(audit: &Value) -> i64 {
    let block = match audit.get("non_conjecture_axioms") {
        Some(v) => v,
        None => return 0,
    };
    let per_prefix = block
        .get("per_prefix")
        .and_then(|v| v.as_object())
        .expect("non_conjecture_axioms.per_prefix must be an object");
    let mut total: i64 = 0;
    for (prefix, entry) in per_prefix {
        let count = entry
            .get("count")
            .and_then(|v| v.as_i64())
            .unwrap_or_else(|| panic!("per_prefix.{prefix}.count must be an integer"));
        assert!(count >= 0, "per_prefix.{prefix}.count is negative: {count}",);
        total += count;
    }
    total
}

/// #3641 acceptance criterion: `sum(conjectures[].axioms) ==
/// total_domain_axioms`. The top-level `total_domain_axioms` is a pure sum
/// of per-conjecture rows (both are filtered by `conjecture_axiom_prefixes`
/// in `gamma_crown_verify.rs`). A delta between them indicates per-row vs
/// top-level hand-maintained drift of the kind #3613/#3640 fixed.
#[test]
fn conjecture_row_sum_equals_top_level_total_domain_axioms() {
    let audit = load_audit_json();
    let conjectures = audit
        .get("conjectures")
        .and_then(|v| v.as_object())
        .expect("axiom_audit.json: 'conjectures' must be an object");

    let row_sum = sum_conjecture_field(conjectures, "axioms");
    let top = audit
        .get("total_domain_axioms")
        .and_then(|v| v.as_i64())
        .expect("total_domain_axioms must be a non-null integer");

    assert_eq!(
        row_sum, top,
        "data/axiom_audit.json: sum(conjectures[].axioms)={row_sum} != \
         total_domain_axioms={top}. Run \
         `python3 -m scripts.axiom_audit.reconcile --check \
         --snapshot <verify_gamma_crown.json>` to re-reconcile rows.",
    );
}

/// Complementary test for `theorems`. Same invariant as above (#3640).
#[test]
fn conjecture_row_sum_equals_top_level_total_theorems() {
    let audit = load_audit_json();
    let conjectures = audit
        .get("conjectures")
        .and_then(|v| v.as_object())
        .expect("axiom_audit.json: 'conjectures' must be an object");

    let row_sum = sum_conjecture_field(conjectures, "theorems");
    let top = audit
        .get("total_theorems")
        .and_then(|v| v.as_i64())
        .expect("total_theorems must be a non-null integer");

    assert_eq!(
        row_sum, top,
        "data/axiom_audit.json: sum(conjectures[].theorems)={row_sum} != \
         total_theorems={top}.",
    );
}

/// #3641 acceptance criterion: `sum(rows.axioms) +
/// non_conjecture_axioms.axioms_total == total_all_axioms`. `total_all_axioms`
/// is the kernel-wide companion aggregate from Option B in
/// `designs/2026-04-20-axiom-audit-reconciliation.md`. When
/// `non_conjecture_axioms` is absent the block is 0 by construction.
#[test]
fn conjecture_row_sum_plus_non_conjecture_equals_total_all_axioms() {
    let audit = load_audit_json();
    let conjectures = audit
        .get("conjectures")
        .and_then(|v| v.as_object())
        .expect("axiom_audit.json: 'conjectures' must be an object");

    let row_sum = sum_conjecture_field(conjectures, "axioms");
    let non_conj = sum_non_conjecture_axioms(&audit);
    let total_all = audit
        .get("total_all_axioms")
        .and_then(|v| v.as_i64())
        .expect("total_all_axioms must be a non-null integer");

    assert_eq!(
        row_sum + non_conj,
        total_all,
        "data/axiom_audit.json: sum(conjectures[].axioms)={row_sum} + \
         non_conjecture_axioms={non_conj} != total_all_axioms={total_all}. \
         Run `python3 -m scripts.axiom_audit.aggregates` \
         to refresh aggregates.",
    );
}

/// `total_all_axioms >= total_domain_axioms` by construction (#3641). The
/// non-conjecture delta is non-negative because it counts axioms OUTSIDE
/// conjecture prefixes (see `conjecture_axiom_prefixes()` in
/// `gamma_crown_verify.rs`) rather than a signed drift.
#[test]
fn total_all_axioms_is_at_least_total_domain_axioms() {
    let audit = load_audit_json();
    let total_all = audit
        .get("total_all_axioms")
        .and_then(|v| v.as_i64())
        .expect("total_all_axioms must be a non-null integer");
    let total_domain = audit
        .get("total_domain_axioms")
        .and_then(|v| v.as_i64())
        .expect("total_domain_axioms must be a non-null integer");

    assert!(
        total_all >= total_domain,
        "total_all_axioms ({total_all}) < total_domain_axioms ({total_domain}) \
         violates #3641 Option B invariant: non-conjecture delta is non-negative.",
    );
}

/// #3641 acceptance criterion: when `total_all_axioms > total_domain_axioms`
/// (i.e. the kernel has non-conjecture-prefix axioms), the `non_conjecture_axioms`
/// block MUST be present and its per-prefix counts MUST sum to the delta.
/// Prevents silent drift where the companion aggregate claims additional
/// axioms but the per-prefix breakdown is missing or stale.
#[test]
fn non_conjecture_block_is_present_when_delta_is_non_zero() {
    let audit = load_audit_json();
    let total_all = audit
        .get("total_all_axioms")
        .and_then(|v| v.as_i64())
        .expect("total_all_axioms must be a non-null integer");
    let total_domain = audit
        .get("total_domain_axioms")
        .and_then(|v| v.as_i64())
        .expect("total_domain_axioms must be a non-null integer");
    let delta = total_all - total_domain;

    if delta == 0 {
        // Block may be absent or present-with-all-zero counts.
        if let Some(block) = audit.get("non_conjecture_axioms") {
            let per_prefix_sum = sum_non_conjecture_axioms(&audit);
            assert_eq!(
                per_prefix_sum, 0,
                "non_conjecture_axioms present but per_prefix sum={per_prefix_sum} \
                 disagrees with total_all_axioms - total_domain_axioms = 0",
            );
            let _ = block; // acknowledge the variable
        }
    } else {
        let block = audit.get("non_conjecture_axioms").unwrap_or_else(|| {
            panic!(
                "total_all_axioms ({total_all}) exceeds total_domain_axioms ({total_domain}) \
                 by {delta}, but 'non_conjecture_axioms' block is absent. #3641 requires the \
                 per-prefix breakdown to accompany any non-zero delta."
            )
        });
        let per_prefix = block
            .get("per_prefix")
            .and_then(|v| v.as_object())
            .unwrap_or_else(|| panic!("non_conjecture_axioms.per_prefix must be an object"));
        assert!(
            !per_prefix.is_empty(),
            "non_conjecture_axioms.per_prefix is empty but delta={delta} — \
             populate with the enumerated non-conjecture prefix counts (#3641).",
        );
        let per_prefix_sum = sum_non_conjecture_axioms(&audit);
        assert_eq!(
            per_prefix_sum, delta,
            "non_conjecture_axioms.per_prefix sum={per_prefix_sum} != \
             total_all_axioms - total_domain_axioms = {delta}",
        );
    }
}
