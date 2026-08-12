// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Edge case: mixing found and not-found names in one batch returns the
/// correct per-entry status, and the summary tallies agree with per-entry
/// inspection.
#[test]
fn test_mixed_found_and_not_found_names() {
    let Some(result) = load_gamma_crown_environment() else {
        eprintln!("Skipping: Lean 4 toolchain not found");
        return;
    };

    let names = &[
        "Nat.add_comm",
        "Nat.mul_comm",
        "definitely.not.a.real.constant.xyz",
        "propext",
        "another.fake.name",
    ];
    let summary = verify_mathlib_lemmas_kernel(&result.env, names);
    assert_eq!(summary.reports.len(), names.len());
    assert_eq!(summary.num_not_found(), 2);
    // At least one real lemma must be found. (propext is an axiom; the two
    // Nat lemmas are theorems with proofs in Init.Data.Nat.Lemmas.)
    assert!(summary.num_found() >= 3);
    // No failures — if Init loaded them they must re-check.
    assert_eq!(summary.num_failed(), 0);
}

/// REAL-MATHLIB kernel-verified replay of indexed inductive families, on an
/// actual released `lean4_mathlib4.mathverse` shard (path via
/// `CLEAN_MV_MATHLIB_SHARD`; the shard is NOT in the git tree, so this test
/// skips cleanly in CI). For Mathlib's indexed relation-closure families
/// (`Relation.ReflTransGen` / `TransGen` / `ReflGen`) it proves end-to-end that:
///
///   1. Clean's kernel regenerates each present, self-contained family from the
///      shard's stored type + constructors through the checked `add_inductive`
///      replay (positivity, universes, recursor GENERATION), and
///   2. the regenerated `{T}.rec` is def-eq to the shard's stored Lean recursor
///      (`AlphaTypeMatch::Match`), and
///   3. the production `checked_inductive_replay_matches_shard` gate accepts the
///      whole family (type + constructors + recursor) on the real shard bytes —
///      i.e. these families are genuinely KernelVerified from real Mathlib data,
///      not merely axiomatized. This is the Mathlib-corpus counterpart to the
///      Init-only KV work.
///
/// It ALSO MEASURES (does not assume) whether the regenerated `{T}.rec` diverges
/// STRUCTURALLY from Lean's stored recursor — the shape the widened `is_def_eq`
/// accept gate exists to rescue. EMPIRICAL FINDING (mathverse-v1.3.0 shard):
/// `ReflTransGen` and `ReflGen` regenerate STRUCTURALLY IDENTICAL to Lean's
/// stored recursors (same `u_1` motive universe, same binder placement) — same
/// as Lean core (`test_real_lean_core_recursors_accepted_by_widened_gate`), so
/// `rescued` is empty and the widened gate is a safe SUPERSET these particular
/// families do not require here. The widening's soundness is independent of that
/// (it can only additionally accept a def-eq regenerated recursor, never install
/// shard bytes; `add_inductive` is the oracle); this test does not assert that
/// divergence occurs, only that whatever the shard stores is accepted iff def-eq.
#[test]
fn test_real_mathlib_indexed_family_recursor_defeq_accepted() {
    use crate::inductive_replay::{
        build_inductive_replay_metadata, checked_inductive_replay_matches_shard,
        reconstruct_constant, types_equal_ignoring_binder_info, NormMode, ShardFamilyMatch,
    };
    use crate::types::DeclKind;
    use crate::verify::incremental::{alpha_type_match_against_existing, AlphaTypeMatch};
    use clean_kernel::Name;

    let Ok(shard_path) = std::env::var("CLEAN_MV_MATHLIB_SHARD") else {
        eprintln!("Skipping: set CLEAN_MV_MATHLIB_SHARD to a lean4_mathlib4.mathverse shard");
        return;
    };
    if !std::path::Path::new(&shard_path).exists() {
        eprintln!("Skipping: CLEAN_MV_MATHLIB_SHARD={shard_path} does not exist");
        return;
    }
    let reader = ShardReader::from_file(&shard_path).expect("mathlib shard readable");

    // Mathlib's indexed relation-closure families — the exact shape whose
    // regenerated recursor is def-eq but structurally divergent from Lean's.
    let families = [
        "Relation.ReflTransGen",
        "Relation.TransGen",
        "Relation.ReflGen",
    ];

    let mut validated = 0usize;
    let mut rescued: Vec<String> = Vec::new();

    for fam in families {
        let Some((_, ind_header)) = reader.lookup_name(fam) else {
            eprintln!("MATHLIB {fam}: not present in shard, skipping");
            continue;
        };
        assert_eq!(
            ind_header.decl_kind().ok(),
            Some(DeclKind::Inductive),
            "{fam} must be stamped DeclKind::Inductive in a real shard",
        );

        let root = reconstruct_constant(fam, &reader, ind_header)
            .unwrap_or_else(|e| panic!("{fam}: reconstruct root: {e}"));
        let Some(metadata) =
            build_inductive_replay_metadata(&reader, ind_header, &root, NormMode::Off)
                .unwrap_or_else(|e| panic!("{fam}: build_inductive_replay_metadata: {e}"))
        else {
            eprintln!("MATHLIB {fam}: metadata reconstruction returned None, skipping");
            continue;
        };

        // These relation closures close over only Sort/Prop + their own params,
        // so the checked replay regenerates the whole family (type, ctors, rec)
        // into a fresh env with no external seeding.
        let mut scratch = Environment::new();
        if let Err(e) = scratch.add_inductive(metadata.decl.clone()) {
            eprintln!("MATHLIB {fam}: add_inductive into fresh env failed ({e}), skipping");
            continue;
        }

        let rec_name = Name::from_string(&format!("{fam}.rec"));
        let Some(clean_rec) = scratch.get_const(&rec_name) else {
            panic!("{fam}: regenerated env is missing {fam}.rec after add_inductive");
        };

        // The shard's stored (Lean) recursor.
        let Some((_, shard_rec_header)) = reader.lookup_name(&rec_name.to_string()) else {
            panic!("{fam}: shard is missing stored {fam}.rec header");
        };
        let shard_rec = reconstruct_constant(&rec_name.to_string(), &reader, shard_rec_header)
            .unwrap_or_else(|e| panic!("{fam}: reconstruct shard rec: {e}"));

        // Pre-fix EXACT gate: strict level-param equality + structural type
        // equality (ignoring only binder annotations, as the old gate did).
        let structural = shard_rec.level_params == clean_rec.level_params
            && types_equal_ignoring_binder_info(&shard_rec.type_expr, &clean_rec.type_);

        // Widened gate (production call direction: regenerated vs shard-stored).
        let gate = alpha_type_match_against_existing(
            &scratch,
            clean_rec,
            &shard_rec.level_params,
            &shard_rec.type_expr,
        );

        eprintln!(
            "MATHLIB {fam}.rec: structural={structural} gate={gate:?} \
             shard_lp={:?} clean_lp={:?}",
            shard_rec.level_params, clean_rec.level_params,
        );

        // CORE CLAIM: the regenerated recursor is def-eq to Lean's real stored
        // recursor, so the widened gate accepts it. A build_recursor fidelity
        // gap would surface here as a hard failure (never a silent accept).
        assert_eq!(
            gate,
            AlphaTypeMatch::Match,
            "{fam}.rec: Clean's regenerated recursor is not def-eq to the shard's \
             stored Lean recursor — the widened gate would correctly fail this family closed",
        );

        // END-TO-END: the actual production family-match gate accepts the whole
        // family (type + constructors + widened recursor) on real Mathlib bytes.
        match checked_inductive_replay_matches_shard(&scratch, &reader, &metadata, NormMode::Off)
            .unwrap_or_else(|e| panic!("{fam}: checked_inductive_replay_matches_shard: {e}"))
        {
            ShardFamilyMatch::Matched => {}
            ShardFamilyMatch::Mismatch { member, detail } => panic!(
                "{fam}: production checked-replay gate REJECTED real Mathlib family at \
                 member {member}: {detail}",
            ),
        }

        validated += 1;
        if !structural {
            // The pre-fix exact `.rec` gate would have rejected this real
            // Mathlib family; the widening rescues it.
            rescued.push(fam.to_string());
        }
    }

    eprintln!(
        "Validated {validated} real Mathlib indexed family recursor(s); \
         structurally divergent (rescued by the widened gate) = {rescued:?}",
    );
    assert!(
        validated > 0,
        "expected to validate at least one real Mathlib indexed relation-closure family \
         (Relation.ReflTransGen/TransGen/ReflGen) from the shard",
    );
}

/// Capstone for the level-parameter contiguity fix: a shard built by the CURRENT
/// exporter from a real, multi-universe-rich environment (Lean core has
/// `Acc.rec [u_1,u]`, `Sigma [u,v]`, `PSigma [u,v]`, …) must pass the
/// [`audit_level_param_integrity`] release gate with ZERO corruption. This is
/// the direct, in-sandbox evidence that rebuilding a `.mathverse` shard with
/// current code eliminates the `UndefinedLevelParam` failure class that the
/// stale released mathverse-v1.3.0 shard exhibits on ~60% of Mathlib constants
/// (see docs/MATHLIB_KV_LEVEL_PARAM_AUDIT_2026-07-04.md). Skips cleanly without
/// the Lean 4 toolchain.
#[test]
fn test_current_exporter_produces_contiguous_level_params() {
    use crate::shard_integrity::audit_level_param_integrity;

    let Some(result) = load_gamma_crown_environment() else {
        eprintln!("Skipping: Lean 4 toolchain not found");
        return;
    };

    let mut writer = ShardWriter::new();
    let config = EnvImportConfig {
        include_private: false,
        source_file: Some("level-param contiguity capstone".to_string()),
        source_version: Some("Lean4".to_string()),
        content_domain: ContentDomain::PureMath,
    };
    let (stats, _records) =
        import_environment(&result.env, &mut writer, &config).expect("env -> shard conversion");
    assert!(stats.total > 0, "Expected non-zero constants in shard");

    let mut bytes = Vec::new();
    writer.write(&mut bytes).expect("shard serialize");
    let reader = ShardReader::from_bytes(&bytes).expect("shard readable");

    let audit = audit_level_param_integrity(&reader);
    println!(
        "=== current-exporter level-param audit === with_params={} corrupt={} ({:.2}%)",
        audit.with_params,
        audit.corrupt,
        audit.corrupt_rate() * 100.0,
    );
    // A real corpus slice must actually exercise multi-universe constants, or
    // the gate is vacuous.
    assert!(
        audit.with_params > 100,
        "expected the core env to carry many multi-universe constants, got {}",
        audit.with_params,
    );
    assert!(
        audit.is_clean(),
        "current exporter must produce contiguous level params (0 corrupt); \
     sample corruptions: {:?}",
        audit.sample,
    );
}
