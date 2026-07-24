// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ad-hoc large-scale closure-replay run over an external `.jsonl` closure
//! exported from `HOL-Proofs` (see `scripts/isabelle/export_pure_proofs.ML`
//! `export_closures`). Driven by the `ISA_CLOSURE` env var so it is a no-op in
//! normal CI (no giant fixture is committed):
//!
//! ```bash
//! ISA_CLOSURE=/tmp/hol_big_closure.txt \
//!   cargo test -p clean-mathverse --test isabelle_scale_run -- --nocapture
//! ```
//!
//! It reports the honest "verified / total" at corpus-relevant scale and
//! confirms the same soundness invariants as the committed 72-theorem harness:
//! every theorem is either verified-by-the-kernel or rejected-with-a-reason.

use clean_mathverse::hol::isabelle_pure::parse_proven_theorem;
use clean_mathverse::hol::isabelle_pure_verify::{
    import_proven_theorems, import_proven_theorems_streaming,
};
use clean_mathverse::shard::ShardWriter;

#[test]
fn scale_run_if_env_set() {
    let Ok(path) = std::env::var("ISA_CLOSURE") else {
        eprintln!("ISA_CLOSURE not set — scale run skipped (no-op).");
        return;
    };
    // Stream the closure file line-by-line rather than slurping it whole: the
    // dense corpus exports are multi-GB, so a single `read_to_string` would
    // allocate the entire file as one `String` on top of the parsed `Vec`,
    // doubling peak memory and risking OOM. `BufReader::lines` drops each raw
    // line after it is parsed, so peak memory is the parsed corpus alone.
    use std::io::BufRead as _;
    let file = std::fs::File::open(&path).expect("open ISA_CLOSURE file");
    let reader = std::io::BufReader::new(file);
    let theorems: Vec<_> = reader
        .lines()
        .map_while(Result::ok)
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| parse_proven_theorem(&l).ok())
        .collect();

    let mut writer = ShardWriter::new();
    let result = import_proven_theorems(&theorems, &mut writer);

    eprintln!(
        "SCALE RUN: {} parsed, {} KernelVerified, {} rejected",
        theorems.len(),
        result.kernel_verified,
        result.rejected
    );
    eprintln!("rejection reasons: {:?}", result.rejection_reasons);
    if !theorems.is_empty() {
        eprintln!(
            "verified fraction: {:.1}%",
            100.0 * result.kernel_verified as f64 / theorems.len() as f64
        );
    }

    // Optionally persist the verified theorems to a real `.mathverse` shard so
    // the result is literally "Isabelle proofs in Mathverse as KernelVerified".
    if let Ok(out) = std::env::var("ISA_SHARD_OUT") {
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        std::fs::write(&out, &buf).expect("write shard file");
        eprintln!(
            "WROTE shard: {} ({} KernelVerified Isabelle theorems, {} bytes)",
            out,
            result.kernel_verified,
            buf.len()
        );
    }

    // Soundness invariants hold at any scale. The two ledger counters are 0
    // unless `ISA_TRUSTED_LEDGER` is set, so this reduces to the historical
    // `KV + rejected == parsed` on a non-ledger run.
    assert_eq!(
        result.kernel_verified
            + result.kernel_checked_ledger
            + result.ledger_size
            + result.rejected,
        theorems.len()
    );
    assert_eq!(result.kernel_verified, result.names.len());
}

/// Streaming / bounded-memory variant of the scale run, for corpora far larger
/// than RAM (the full HOL-Proofs library). Driven by `ISA_CLOSURE_STREAM` so it
/// is a no-op in normal CI:
///
/// ```bash
/// ISA_CLOSURE_STREAM=/tmp/hol_corpus_grand.txt \
///   cargo test -p clean-mathverse --release --test isabelle_scale_run \
///   stream_run_if_env_set -- --nocapture
/// ```
///
/// Unlike [`scale_run_if_env_set`], this path never holds the whole parsed corpus
/// in memory:
///
/// 1. **Serial-sort (external).** Isabelle assigns proof-term serials in creation
///    order, so a theorem's `PThm` dependencies always have *smaller* serials.
///    Serial-ascending order is therefore a valid topological order
///    (deps-before-uses). We external-sort the corpus by the numeric `serial`
///    field with the OS `sort`, in a separate child process whose memory is
///    independent of the streaming driver's. Every line begins `{"serial":N,...`,
///    so a `sed` prepends `N` as a tab-separated numeric sort key, `sort -s -n`
///    orders stably (preserving original order among equal serials — exactly the
///    batch driver's duplicate tie-break), and `cut -f2-` strips the key back off.
/// 2. **Stream-verify.** [`import_proven_theorems_streaming`] reads the sorted
///    file line-by-line, translating + kernel-checking each theorem against the
///    accumulating environment/closure/class-registry and dropping it immediately.
///    Peak memory is the accumulating state plus one parsed theorem — independent
///    of corpus size.
///
/// Because closure replay is order-independent given deps-before-uses, the
/// `KernelVerified` count MUST match the batch driver's on the same corpus.
#[test]
fn stream_run_if_env_set() {
    let Ok(path) = std::env::var("ISA_CLOSURE_STREAM") else {
        eprintln!("ISA_CLOSURE_STREAM not set — streaming run skipped (no-op).");
        return;
    };

    // Machine-wide verify lock: refuse to run a SECOND verify group concurrently
    // (that is what silently depressed the historical numbers). The lockfile lives
    // in the corpus directory (which always exists); a shard group's children
    // bypass it via `ISA_VERIFY_LOCK=held`, and tests bypass it likewise. Held for
    // the whole run by binding the guard.
    let corpus_dir = std::path::Path::new(&path)
        .parent()
        .map(std::path::Path::to_path_buf)
        .unwrap_or_else(|| std::path::PathBuf::from("."));
    let _verify_lock = clean_mathverse::hol::isabelle_pure_verify::VerifyLock::acquire(
        corpus_dir.join(".clean_verify.lock"),
    )
    .unwrap_or_else(|e| panic!("{e}"));

    // Where to put the serial-sorted file. Caller may override (e.g. a fast
    // scratch disk, or a group leader pinning ONE presorted file its shard children
    // share read-only); the default is PROCESS-UNIQUE so two standalone runs over
    // the same corpus never truncate-rewrite the same scratch path concurrently
    // (the shared-scratch race that corrupted a concurrent slice's input).
    let sorted = std::env::var("ISA_CLOSURE_STREAM_SORTED")
        .unwrap_or_else(|_| format!("{path}.{}.serial_sorted.txt", std::process::id()));

    // `ISA_CLOSURE_STREAM_PRESORTED=1` asserts the input file is already serial-
    // ascending sorted and skips the external sort entirely (in which case
    // `ISA_CLOSURE_STREAM` itself is consumed directly). This is useful to (a)
    // re-run the verify without re-paying the sort, and (b) measure the streaming
    // driver's peak RSS in isolation: `/usr/bin/time -l` aggregates a reaped child
    // process's max RSS into the parent's figure via `getrusage(RUSAGE_CHILDREN)`,
    // so the external `sort`'s large working set would otherwise dominate the
    // reported maximum even though it never coexists with the verify allocations.
    let presorted = std::env::var("ISA_CLOSURE_STREAM_PRESORTED").is_ok();
    let sorted = if presorted {
        path.clone()
    } else {
        // External, stable, numeric sort by the leading `serial` field, in a
        // separate child process. `LC_ALL=C` for a byte-stable, locale-independent
        // sort. The key is the digits after `{"serial":`; `sort -s` (stable)
        // preserves the original line order among equal serials, matching the
        // batch driver's last-occurrence/closure tie-break for duplicate serials.
        // A literal tab joins the numeric key to the JSON body; `cut -f2-` (tab
        // default) strips it back. `sort` uses default whitespace field splitting,
        // so field 1 is the serial digits regardless of shell tab-escaping support.
        let pipeline = format!(
            "set -o pipefail; LC_ALL=C sed -E 's/^\\{{\"serial\":([0-9]+),.*/\\1\\t&/' {q} | \
             LC_ALL=C sort -s -k1,1n -T \"$(dirname {qs})\" | \
             LC_ALL=C cut -f2- > {qs}",
            q = shell_quote(&path),
            qs = shell_quote(&sorted),
        );
        let status = std::process::Command::new("sh")
            .arg("-c")
            .arg(&pipeline)
            .status()
            .expect("spawn external sort");
        assert!(status.success(), "external serial-sort failed: {status}");
        sorted
    };

    // Total line count (for the verified-fraction report) — counted by streaming,
    // never materialised.
    let total_lines = count_nonempty_lines(&sorted);

    let mut writer = ShardWriter::new();

    // `ISA_SHARDS=N` runs the WHOLE N-way shard group end-to-end in THIS process
    // (the group leader / single-command surface): it fans N big-stack shard
    // threads out over the corpus, writes each `shard_k.json` under
    // `ISA_SHARD_GROUP_DIR` (default: the corpus directory), and merges them into
    // the single verdict stream a serial run would produce
    // (`merge_shard_verdicts`) — byte-identical by construction. The harness
    // already holds the machine-wide verify lock (acquired above), so the group
    // driver does NOT re-acquire it (`acquire_lock = false`). `ISA_SHARD_PREPASS_AUTO`
    // exports the shared pre-pass state once and hands it to every shard (skips
    // the O(T) registry scan per shard); `ISA_SHARD_MERGE_OUT` writes the merged
    // JSON. Mutually exclusive with the single-shard `ISA_SHARD` below.
    if let Ok(nspec) = std::env::var("ISA_SHARDS") {
        use clean_mathverse::hol::isabelle_pure_verify::{
            run_shard_group_in_process, ShardGroupOpts,
        };
        let n: usize = nspec
            .trim()
            .parse()
            .expect("ISA_SHARDS must be a positive integer");
        let group_dir = std::env::var("ISA_SHARD_GROUP_DIR")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|_| corpus_dir.join("shard_group"));
        let mut opts = ShardGroupOpts::new(n, &group_dir);
        opts.acquire_lock = false; // the harness already holds the lock
        opts.prepass = std::env::var_os("ISA_SHARD_PREPASS_AUTO").is_some();
        opts.merged_out = std::env::var("ISA_SHARD_MERGE_OUT")
            .ok()
            .map(std::path::PathBuf::from);
        // `ISA_SHARD_MATHVERSE_OUT`: fan each shard's OWN range to a
        // `shard_k.mathverse` and merge them into this one provenance shard
        // (equivalent to the unsharded stream's `.mathverse`).
        opts.mathverse_out = std::env::var("ISA_SHARD_MATHVERSE_OUT")
            .ok()
            .map(std::path::PathBuf::from);
        let merged = run_shard_group_in_process(&sorted, &opts)
            .unwrap_or_else(|e| panic!("shard group failed: {e}"));
        eprintln!(
            "SHARD GROUP {n}-way: total_lines={} KernelVerified={} rejected={} (tier-2={} ledger={})",
            merged.total_lines,
            merged.kernel_verified,
            merged.rejected,
            merged.kernel_checked_ledger,
            merged.ledger_size,
        );
        assert_eq!(
            merged.kernel_verified
                + merged.rejected
                + merged.kernel_checked_ledger
                + merged.ledger_size,
            merged.total_lines,
            "merged group verdicts must account for every corpus line exactly once"
        );
        return;
    }

    // `ISA_SHARD=k/N` verifies only shard k's contiguous line range and writes its
    // mergeable verdicts to `ISA_SHARD_VERDICTS_OUT`. Every shard runs the full
    // deterministic replay and emits only its range (see `shard_verify`), so the
    // union merged by `merge_shard_verdicts` is byte-identical to a single run.
    // A shard run's aggregate is its RANGE, not the whole corpus, so it returns
    // early (the whole-corpus fraction/soundness asserts below do not apply).
    // `ISA_SHARD_PREPASS=<snapshot>` loads a leader-exported pre-pass state
    // (`export_prepass_snapshot`) so this child skips the O(T) registry scan —
    // the subprocess group driver injects it into each child.
    if let Ok(shard_spec) = std::env::var("ISA_SHARD") {
        use clean_mathverse::hol::isabelle_pure_verify::{
            import_proven_theorems_streaming_shard_emit, ShardSpec,
        };
        let spec = ShardSpec::parse(&shard_spec).expect("ISA_SHARD must be k/N");
        // `ISA_SHARD_MATHVERSE_OUT` (optional): emit THIS shard's own serial
        // range's KernelVerified constants to a per-shard `.mathverse` artifact
        // the group leader later merges (`merge_shard_mathverse`) into one shard
        // equivalent to the unsharded stream. Absent = verdicts only, unchanged.
        let prepass = std::env::var("ISA_SHARD_PREPASS")
            .ok()
            .filter(|p| !p.is_empty());
        let mathverse_out = std::env::var("ISA_SHARD_MATHVERSE_OUT").ok();
        let verds = import_proven_theorems_streaming_shard_emit(
            &sorted,
            &mut writer,
            spec,
            prepass.as_deref().map(std::path::Path::new),
            mathverse_out.as_deref().map(std::path::Path::new),
        )
        .expect("sharded verify I/O");
        eprintln!(
            "SHARD {}/{}: lines [{}, {}) of {} — KernelVerified={} rejected={}",
            spec.k,
            spec.n,
            verds.lo,
            verds.hi,
            verds.total_lines,
            verds.kernel_verified(),
            verds.rejected()
        );
        if let Some(mv) = &mathverse_out {
            eprintln!("WROTE shard .mathverse: {mv}");
        }
        if let Ok(out) = std::env::var("ISA_SHARD_VERDICTS_OUT") {
            verds.save(&out).expect("write shard verdicts");
            eprintln!("WROTE shard verdicts: {out}");
        }
        return;
    }

    // `ISA_PARALLEL_WORKERS=N` (N>0) routes through the parallel driver —
    // verdict-identical by construction (parse+translate fan out; the kernel
    // loop stays serial on the master). Unset/0 = the historical serial driver.
    let parallel_workers: usize = std::env::var("ISA_PARALLEL_WORKERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let result = if parallel_workers > 0 {
        clean_mathverse::hol::isabelle_pure_verify::import_proven_theorems_parallel(
            &sorted,
            &mut writer,
            parallel_workers,
        )
        .expect("parallel verify I/O")
    } else {
        import_proven_theorems_streaming(&sorted, &mut writer).expect("streaming verify I/O")
    };

    eprintln!(
        "STREAM RUN: {} lines, {} KernelVerified, {} rejected",
        total_lines, result.kernel_verified, result.rejected
    );
    // Three-tier trusted-ledger breakdown (`ISA_TRUSTED_LEDGER`). Printed only
    // when the lane produced anything, so a non-ledger run's stderr is
    // unchanged (the counters are 0/empty and this line is skipped). tier-1 is
    // the `KernelVerified` count above; tier-2 (`KernelCheckedConditional`) is
    // kernel-re-checked modulo the ledger; the ledger axioms are statement-only
    // restatements, counted here and NOWHERE in KernelVerified.
    if result.kernel_checked_ledger != 0 || result.ledger_size != 0 {
        eprintln!(
            "TWO-TIER: {} KernelVerified (tier-1), {} KernelCheckedConditional (tier-2), \
             {} trusted-ledger axioms, {} rejected",
            result.kernel_verified,
            result.kernel_checked_ledger,
            result.ledger_size,
            result.rejected
        );
    }
    eprintln!("rejection reasons: {:?}", result.rejection_reasons);

    // Opt-in fine-grained breakdown: when `ISA_REJECT_SPECIFICS` is set, the
    // driver tallies the normalized full-message prefix of each rejection. Print
    // it frequency-ranked (most-frequent first) — the concrete "what to support
    // next" list. `ISA_REJECT_SPECIFICS_TOP` caps how many rows print (default 30).
    if !result.rejection_specifics.is_empty() {
        let top: usize = std::env::var("ISA_REJECT_SPECIFICS_TOP")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(30);
        let mut ranked: Vec<(&String, &usize)> = result.rejection_specifics.iter().collect();
        // Sort by count descending, then key ascending for a stable tie-break.
        ranked.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
        eprintln!(
            "REJECTION SPECIFICS (top {} of {} distinct):",
            top.min(ranked.len()),
            ranked.len()
        );
        for (rank, (key, count)) in ranked.iter().take(top).enumerate() {
            eprintln!("  #{:<3} {:>10}  {}", rank + 1, count, key);
        }
    }
    if total_lines != 0 {
        eprintln!(
            "verified fraction: {:.1}%",
            100.0 * result.kernel_verified as f64 / total_lines as f64
        );
    }

    if let Ok(out) = std::env::var("ISA_SHARD_OUT") {
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        std::fs::write(&out, &buf).expect("write shard file");
        eprintln!(
            "WROTE shard: {} ({} KernelVerified Isabelle theorems, {} bytes)",
            out,
            result.kernel_verified,
            buf.len()
        );
    }

    // Same soundness invariants as the batch driver at any scale. Under the
    // two-tier ledger lane a line can also be tier-2 or a ledger axiom; both
    // counters are 0 when `ISA_TRUSTED_LEDGER` is unset, so this reduces to the
    // historical `KV + rejected == lines` on a non-ledger run.
    assert_eq!(
        result.kernel_verified
            + result.kernel_checked_ledger
            + result.ledger_size
            + result.rejected,
        total_lines
    );
    assert_eq!(result.kernel_verified, result.names.len());
}

/// **Merge verb.** `ISA_SHARD_MERGE=<path1,path2,…>` reads the per-shard
/// `ShardVerdicts` JSON artifacts a group's shards wrote (via
/// `ISA_SHARD_VERDICTS_OUT`), combines them with `merge_shard_verdicts` into the
/// single verdict stream byte-identical to a serial run, and writes the merged
/// `MergedVerdicts` JSON to `ISA_SHARD_MERGE_OUT` (default: stdout summary only).
/// No-op when `ISA_SHARD_MERGE` is unset.
#[test]
fn merge_shards_if_env_set() {
    let Ok(list) = std::env::var("ISA_SHARD_MERGE") else {
        eprintln!("ISA_SHARD_MERGE not set — merge verb skipped (no-op).");
        return;
    };
    use clean_mathverse::hol::isabelle_pure_verify::{merge_shard_verdicts, ShardVerdicts};
    let parts: Vec<ShardVerdicts> = list
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(|p| ShardVerdicts::load(p).unwrap_or_else(|e| panic!("load shard {p}: {e}")))
        .collect();
    assert!(!parts.is_empty(), "ISA_SHARD_MERGE listed no shard files");
    let merged = merge_shard_verdicts(&parts).unwrap_or_else(|e| panic!("merge failed: {e}"));
    eprintln!(
        "MERGED {} shards: total_lines={} KernelVerified={} rejected={} (tier-2={} ledger={})",
        parts.len(),
        merged.total_lines,
        merged.kernel_verified,
        merged.rejected,
        merged.kernel_checked_ledger,
        merged.ledger_size,
    );
    // Soundness invariant, reconstructed from the merge.
    assert_eq!(
        merged.kernel_verified
            + merged.rejected
            + merged.kernel_checked_ledger
            + merged.ledger_size,
        merged.total_lines,
        "merged verdicts must account for every corpus line exactly once"
    );
    if let Ok(out) = std::env::var("ISA_SHARD_MERGE_OUT") {
        let bytes = serde_json::to_vec_pretty(&merged).expect("serialize merged verdicts");
        std::fs::write(&out, bytes).expect("write merged verdicts");
        eprintln!("WROTE merged verdicts: {out}");
    }
}

/// Count non-empty lines of a file by streaming (never materialising it).
fn count_nonempty_lines(path: &str) -> usize {
    use std::io::BufRead as _;
    let file = std::fs::File::open(path).expect("open serial-sorted file for line count");
    std::io::BufReader::new(file)
        .lines()
        .map_while(Result::ok)
        .filter(|l| !l.trim().is_empty())
        .count()
}

/// Minimal single-quote shell escaping for a path embedded in an `sh -c` string.
fn shell_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', "'\\''"))
}

/// Per-serial verdict harness for slice A/B validation (reprove-lane rounds).
/// Driven by `ISA_PERLINE` (a small `.jsonl` slice); prints one
/// `VERDICT<TAB>serial<TAB>KV|REJECT[<TAB>reason]` line per input, by importing
/// each theorem in its own fresh environment (valid for statement-self-contained
/// hole lines whose fabricated proof needs no corpus dependency). Toggle the
/// reprove lane with `ISA_REPROVE=0` (control) vs `ISA_REPROVE=1` (treatment).
/// No-op when unset.
#[test]
fn perline_verdicts_if_env_set() {
    let Ok(path) = std::env::var("ISA_PERLINE") else {
        eprintln!("ISA_PERLINE not set — per-line harness skipped (no-op).");
        return;
    };
    use std::io::BufRead as _;
    let file = std::fs::File::open(&path).expect("open ISA_PERLINE file");
    let mut kv = 0usize;
    let mut rej = 0usize;
    for line in std::io::BufReader::new(file).lines().map_while(Result::ok) {
        if line.trim().is_empty() {
            continue;
        }
        let Ok(thm) = parse_proven_theorem(&line) else {
            eprintln!("PARSE-ERR\t{}", &line[..line.len().min(80)]);
            continue;
        };
        let serial = thm.serial;
        let mut writer = ShardWriter::new();
        let result = import_proven_theorems(std::slice::from_ref(&thm), &mut writer);
        if result.kernel_verified == 1 {
            kv += 1;
            eprintln!("VERDICT\t{serial}\tKV");
        } else {
            rej += 1;
            let reason = result
                .rejection_reasons
                .keys()
                .next()
                .cloned()
                .unwrap_or_default();
            eprintln!("VERDICT\t{serial}\tREJECT\t{reason}");
        }
    }
    eprintln!("PERLINE-SUMMARY\tKV={kv}\tREJECT={rej}");
}
