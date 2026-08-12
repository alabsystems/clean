// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Global, dependency-closed corpus verification (`--corpus`).
///
/// Loads EVERY discovered `.mathverse` shard into one merged `MathverseLibrary`
/// and re-verifies the whole corpus in a single prelude-seeded kernel
/// environment, in global topological order. Unlike `--incremental` (which runs
/// each shard against its own fresh prelude env), this resolves CROSS-SHARD
/// references — a constant in one shard whose type or value depends on a
/// constant defined in another — because the merged library puts every
/// dependency in one in-arena dependency graph.
pub(super) fn cmd_verify_corpus(
    shard_dir: &Path,
    emit_verified: Option<&Path>,
    repair_levels: bool,
    elide_proofs: clean_kernel::env::ProofValueElision,
) {
    use clean_mathverse::library::MathverseLibrary;
    use clean_mathverse::shard::ShardReader;
    use clean_mathverse::shard_verify::discover_mathverse_files;
    use clean_mathverse::trust::policy::TrustPolicy;
    use clean_mathverse::verify::incremental::{
        verify_corpus_incremental_repaired_bounded, verify_corpus_incremental_with_env,
        InductiveReplayPolicy,
    };
    use clean_mathverse::verify::kernel_verified_manifest::KernelVerifiedManifest;

    println!("=== Mathverse Global Corpus Kernel Verification ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files\n", mathverse_files.len());

    let start = Instant::now();

    // Merge every shard into one globally-indexed library.
    let mut library = MathverseLibrary::new(TrustPolicy::permissive());
    let mut loaded = 0usize;
    for path in &mathverse_files {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let reader = match ShardReader::from_file(path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("  SKIP {name}: {e}");
                continue;
            }
        };
        match library.load_shard(&reader) {
            Ok(added) => {
                loaded += 1;
                println!("  Loaded {name}: {added} constants");
            }
            Err(e) => eprintln!("  SKIP {name}: {e}"),
        }
    }
    println!(
        "\n  Merged {loaded} shards into {} constants\n",
        library.constant_count()
    );

    let prelude = clean_kernel::Environment::try_with_prelude_for_import()
        .expect("kernel prelude environment");
    if elide_proofs != clean_kernel::env::ProofValueElision::None {
        println!(
            "  Bounded-memory elision: {elide_proofs:?} (proof VALUES dropped periodically; \
             types retained)\n"
        );
    }
    let (env, report) = if repair_levels {
        // Olean-sourced corpora MUST use LeanFaithful: Clean's own generated
        // convenience definitions (noConfusion/casesOn/…) otherwise shadow the
        // shard's Lean-stored spellings and cascade-fail downstream re-checks.
        let (env, report, repair) = verify_corpus_incremental_repaired_bounded(
            &library,
            prelude,
            InductiveReplayPolicy::LeanFaithful,
            elide_proofs,
        );
        println!(
            "  Level-param repair: {} examined, {} repaired, {} unrepairable\n",
            repair.examined, repair.repaired, repair.unrepairable
        );
        (env, report)
    } else if elide_proofs != clean_kernel::env::ProofValueElision::None {
        // Non-repair bounded path: repair is a no-op on a clean shard, so route
        // through the same bounded entry point to get periodic elision.
        let (env, report, _repair) = verify_corpus_incremental_repaired_bounded(
            &library,
            prelude,
            InductiveReplayPolicy::LeanFaithful,
            elide_proofs,
        );
        (env, report)
    } else {
        verify_corpus_incremental_with_env(&library, prelude)
    };

    print_corpus_summary(&report, start.elapsed());

    // BEDROCK = KernelVerified AND `axiom_deps` empty (transitive non-foundational
    // axiom closure ⊆ {propext, Quot.sound, Classical.choice}). KernelVerified
    // alone only means the value typechecked — a Definition whose body references
    // an assumed F* axiom typechecks but is NOT bedrock. This is the honest line:
    // we count only the constants that genuinely reduce to the 3 axioms.
    //
    // `axiom_deps` walks each constant's stored VALUE to find the axioms it
    // reaches. Under proof-value elision those values are dropped, so the walk
    // under-counts axiom dependencies and would OVER-report bedrock (an unsound
    // floor). We therefore only print bedrock when nothing was elided; the
    // kernel-verified count above is unaffected (it is decided at check time,
    // before any elision) and remains a sound LOWER bound under elision.
    if elide_proofs == clean_kernel::env::ProofValueElision::None {
        let bedrock: usize = report
            .kernel_verified_names
            .iter()
            .filter(|n| {
                env.axiom_deps(&clean_kernel::Name::from_string(n))
                    .map(|d| d.is_empty())
                    .unwrap_or(false)
            })
            .count();
        println!(
            "  └─ of which BEDROCK:  {bedrock} (axiom_deps ⊆ propext / Quot.sound / Classical.choice)"
        );
    } else {
        println!(
            "  └─ BEDROCK not computed under --elide-proofs (elided values make axiom_deps \
             under-count); kernel-verified count above is a sound lower bound"
        );
    }

    // Failure taxonomy (diagnostic, opt-in via CLEAN_MV_FAILDUMP). Groups every
    // failure / masked-failure reason into an error CLASS (the message up to its
    // first ':' or 48 chars) and prints the largest buckets, so the dominant
    // failure mode across a large corpus is visible without eyeballing 500k
    // individual errors. If CLEAN_MV_FAILDUMP names a path, the full
    // `(name, reason)` list is written there for drill-down.
    if let Ok(dump_target) = std::env::var("CLEAN_MV_FAILDUMP") {
        let class_of = |msg: &str| -> String {
            let head = msg.split([':', '(']).next().unwrap_or(msg).trim();
            head.chars().take(48).collect::<String>()
        };
        let mut hist: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for (_, reason) in &report.failures {
            *hist.entry(class_of(reason)).or_insert(0) += 1;
        }
        let mut ranked: Vec<(String, usize)> = hist.into_iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        println!(
            "\n=== Failure taxonomy ({} failed) ===",
            report.failures.len()
        );
        for (class, count) in ranked.iter().take(30) {
            println!("  {count:>8}  {class}");
        }
        // Masked failures (a claimed value the kernel REJECTED) are the highest-
        // integrity concern; class them separately.
        if !report.axiom_fallback_names.is_empty() {
            let mut mhist: std::collections::HashMap<String, usize> =
                std::collections::HashMap::new();
            for (_, reason) in &report.axiom_fallback_names {
                *mhist.entry(class_of(reason)).or_insert(0) += 1;
            }
            let mut mranked: Vec<(String, usize)> = mhist.into_iter().collect();
            mranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            println!(
                "\n=== Masked-failure taxonomy ({} axiom-fallback with rejected value) ===",
                report.axiom_fallback_names.len()
            );
            for (class, count) in mranked.iter().take(20) {
                println!("  {count:>8}  {class}");
            }
        }
        if !dump_target.trim().is_empty() {
            use std::io::Write as _;
            match std::fs::File::create(&dump_target) {
                Ok(mut f) => {
                    for (name, reason) in &report.failures {
                        let _ = writeln!(f, "FAIL\t{name}\t{reason}");
                    }
                    for (name, reason) in &report.axiom_fallback_names {
                        let _ = writeln!(f, "MASKED\t{name}\t{reason}");
                    }
                    println!("\n  Wrote full failure list to {dump_target}");
                }
                Err(e) => eprintln!("\n  Warning: failed to write faildump {dump_target}: {e}"),
            }
        }
    }

    // Optionally record exactly which constants Clean's kernel re-verified, as a
    // non-destructive sidecar (the shards themselves are not rewritten).
    if let Some(path) = emit_verified {
        let manifest =
            KernelVerifiedManifest::from_report(&shard_dir.display().to_string(), loaded, &report);
        match manifest.write_to_file(path) {
            Ok(()) => println!(
                "\n  Wrote {} kernel-verified constant names to {}",
                manifest.kernel_verified_names.len(),
                path.display()
            ),
            Err(e) => eprintln!("\n  Warning: failed to write kernel-verified manifest: {e}"),
        }
    }

    if report.failed > 0 || report.reconstruct_failed > 0 {
        std::process::exit(1);
    }
}

fn print_corpus_summary(
    report: &clean_mathverse::verify::incremental::IncrementalVerifyReport,
    elapsed: std::time::Duration,
) {
    println!("=== Global Corpus Verification Summary ===");
    println!("  Total constants:      {}", report.total);
    println!("  Kernel verified:      {}", report.kernel_verified);
    println!("  Axiom-accepted:       {}", report.axiom_accepted);
    println!(
        "  Axiom-fallback:       {} (claimed value did NOT typecheck)",
        report.axiom_fallback
    );
    println!("  Failed:               {}", report.failed);
    println!("  Cycle skipped:        {}", report.cycle_skipped);
    println!("  Reconstruct failed:   {}", report.reconstruct_failed);
    println!("  Elapsed:              {:.2}s", elapsed.as_secs_f64());
    if report.total > 0 {
        println!(
            "  Verification rate:    {:.1}%",
            report.kernel_verified as f64 / report.total as f64 * 100.0
        );
    }
}
