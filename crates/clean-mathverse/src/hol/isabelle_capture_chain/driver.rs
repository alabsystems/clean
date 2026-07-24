// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The self-healing execution loop: build each segment, classify the outcome,
//! and apply the response ladder (retry-threads1 → bisect → proofless) on an
//! out-of-store failure — persisting durable state after every transition so
//! `--resume` continues exactly where it left off.

use std::path::{Path, PathBuf};

use super::collect::collect_captures;
use super::error::CaptureChainError;
use super::ladder::{bisect_segment, decide_ladder, LadderAction};
use super::root_gen::segment_root_text;
use super::runner::{classify, BuildInvocation, BuildOutcome, IsabelleBuildRunner};
use super::spec::ChainSpec;
use super::state::{Attempt, ChainState, SegStatus, SegmentState};
use crate::hol::isabelle_sessions::expand_tilde;

/// Runtime options for a chain run.
#[derive(Debug, Clone)]
pub struct RunOptions {
    /// The work dir holding the durable state file + build log.
    pub work_dir: PathBuf,
    /// Continue from the on-disk state (must match the spec's hash).
    pub resume: bool,
    /// Print the plan and generated ROOTs; build nothing.
    pub dry: bool,
}

/// A compact post-run summary (also used to render the CLI's final line).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CaptureSummary {
    /// Segments in the final (post-rewrite) plan.
    pub total_segments: usize,
    /// Segments built at their intended record_proofs.
    pub ok: usize,
    /// Segments demoted to a proofless (record_proofs=2) bake.
    pub proofless: usize,
    /// Segments halted on a non-OOM failure.
    pub failed: usize,
    /// Total bisects performed.
    pub bisects: usize,
    /// Total threads>1 → threads=1 retries performed.
    pub retries_threads1: usize,
    /// Capture files relocated across all OK builds.
    pub captures_collected: usize,
}

/// The durable file locations under the work dir.
struct ChainPaths {
    state: PathBuf,
    log: PathBuf,
}

fn chain_paths(work_dir: &Path) -> ChainPaths {
    ChainPaths {
        state: work_dir.join("capture_chain_state.json"),
        log: work_dir.join("capture_chain_build.log"),
    }
}

/// Run (or resume, or dry-run) a capture chain with the injected `runner`.
///
/// # Errors
/// Any [`CaptureChainError`]: invalid spec, IO failure, a non-OOM build failure
/// (halts), or an exhausted response ladder (a single proofless theory still
/// OOMs).
pub fn run_capture_chain(
    spec: &ChainSpec,
    opts: &RunOptions,
    runner: &dyn IsabelleBuildRunner,
) -> Result<CaptureSummary, CaptureChainError> {
    spec.validate()?;
    let work_dir = expand_tilde(&opts.work_dir);
    let paths = chain_paths(&work_dir);

    if opts.dry {
        let state = load_or_init(spec, opts, &paths)?;
        print_plan(spec, &state, &work_dir);
        return Ok(summarize(&state, 0));
    }

    ensure_dir(&work_dir)?;
    let mut state = load_or_init(spec, opts, &paths)?;
    state.save(&paths.state)?;
    let collected = run_loop(&mut state, spec, &paths, runner)?;
    Ok(summarize(&state, collected))
}

/// Load prior state for `--resume` (verifying the spec hash) or start fresh.
fn load_or_init(
    spec: &ChainSpec,
    opts: &RunOptions,
    paths: &ChainPaths,
) -> Result<ChainState, CaptureChainError> {
    if paths.state.exists() {
        if opts.resume {
            let state = ChainState::load(&paths.state)?;
            state.ensure_matches(spec)?;
            return Ok(state);
        }
        eprintln!(
            "note: existing state at {} ignored (pass --resume to continue it)",
            paths.state.display()
        );
    } else if opts.resume {
        eprintln!(
            "note: --resume given but no state at {}; starting fresh",
            paths.state.display()
        );
    }
    Ok(ChainState::initial(spec))
}

/// The main index-driven loop. Bisect splices new segments in place; retries and
/// proofless demotions re-run the same index — so the loop only advances on a
/// resolved (Ok/Proofless) segment.
fn run_loop(
    state: &mut ChainState,
    spec: &ChainSpec,
    paths: &ChainPaths,
    runner: &dyn IsabelleBuildRunner,
) -> Result<usize, CaptureChainError> {
    let mut collected = 0usize;
    let mut i = 0usize;
    while i < state.segments.len() {
        if state.segments[i].is_resolved() {
            i += 1;
            continue;
        }
        write_all_roots(state)?;
        let dirs = resolved_dirs(spec, state);
        let inv = build_inv(&state.segments[i], spec, &dirs);
        let session = inv.session.clone();
        let theories = state.segments[i].segment.theories.clone();

        append_log(
            &paths.log,
            &format!(
                "=== [{session}] threads={} record_proofs={} build start (unix {}) ===\n",
                inv.threads,
                inv.record_proofs,
                now_unix_secs()
            ),
        )?;
        eprintln!(
            "[capture-chain] building {session} (threads={}, record_proofs={})",
            inv.threads, inv.record_proofs
        );

        let run = runner.run_build(&inv)?;
        append_log(&paths.log, &run.output)?;
        if !run.output.ends_with('\n') {
            append_log(&paths.log, "\n")?;
        }
        let outcome = classify(&run, &theories);
        let (outcome_str, oom_theory) = match &outcome {
            BuildOutcome::Ok => ("ok", None),
            BuildOutcome::OutOfStore { theory } => ("out_of_store", theory.clone()),
            BuildOutcome::OtherFailure { .. } => ("other_failure", None),
        };
        state.segments[i].attempts.push(Attempt {
            threads: inv.threads,
            record_proofs: inv.record_proofs,
            outcome: outcome_str.to_string(),
            theory: oom_theory.clone(),
            at: now_unix_secs(),
        });
        append_log(
            &paths.log,
            &format!(
                "=== [{session}] outcome={outcome_str} (unix {}) ===\n",
                now_unix_secs()
            ),
        )?;

        match outcome {
            BuildOutcome::Ok => {
                let status = if state.segments[i].ladder.made_proofless {
                    SegStatus::Proofless
                } else {
                    SegStatus::Ok
                };
                state.segments[i].status = status;
                state.save(&paths.state)?;
                let moved = collect_captures(
                    &expand_tilde(&spec.collect.from_dir),
                    &expand_tilde(&spec.collect.to_dir),
                    &spec.collect.glob,
                )?;
                collected += moved;
                eprintln!(
                    "[capture-chain] {session} OK ({status:?}); collected {moved} capture(s)"
                );
                i += 1;
            }
            BuildOutcome::OutOfStore { theory } => {
                apply_ladder(state, i, &session, &theories, theory, paths)?;
                // Never advance i on an OOM: the same index is re-processed as
                // the retried / demoted segment, or (bisect) as the new prefix.
            }
            BuildOutcome::OtherFailure { tail } => {
                state.segments[i].status = SegStatus::Failed;
                state.save(&paths.state)?;
                return Err(CaptureChainError::BuildFailed { session, tail });
            }
        }
    }
    Ok(collected)
}

/// Apply one response-ladder rung to the out-of-store segment at index `i`.
fn apply_ladder(
    state: &mut ChainState,
    i: usize,
    session: &str,
    theories: &[String],
    theory: Option<String>,
    paths: &ChainPaths,
) -> Result<(), CaptureChainError> {
    match decide_ladder(&state.segments[i]) {
        LadderAction::RetryThreads1 => {
            state.segments[i].threads = 1;
            state.segments[i].ladder.retry_threads1 = true;
            state.retries_threads1 += 1;
            state.save(&paths.state)?;
            eprintln!(
                "[capture-chain] {session} ran out of store at threads>1 → retry at threads=1"
            );
        }
        LadderAction::Bisect => {
            let (a, b) = bisect_segment(&state.segments[i]);
            let new_last = b.segment.session.clone();
            for seg in state.segments.iter_mut() {
                if seg.segment.parent == session {
                    seg.segment.parent = new_last.clone();
                }
            }
            eprintln!(
                "[capture-chain] {session} ran out of store → bisect into {} + {} ({} theories)",
                a.segment.session,
                b.segment.session,
                theories.len()
            );
            state.segments.splice(i..=i, [a, b]);
            state.bisects += 1;
            state.save(&paths.state)?;
        }
        LadderAction::Proofless => {
            state.segments[i].segment.record_proofs = 2;
            state.segments[i].ladder.made_proofless = true;
            state.segments[i].proofless_theory = theory.clone();
            state.save(&paths.state)?;
            eprintln!(
                "[capture-chain] {session} (single theory {}) OOMs above record_proofs=2 → \
                 proofless heap-bake",
                theory.as_deref().unwrap_or("<unknown>")
            );
        }
        LadderAction::Exhausted => {
            state.segments[i].status = SegStatus::Failed;
            state.save(&paths.state)?;
            return Err(CaptureChainError::LadderExhausted {
                session: session.to_string(),
                theory: theory.unwrap_or_else(|| "<unknown>".to_string()),
            });
        }
    }
    Ok(())
}

/// All `-d` dirs for a build: global dirs plus every working segment's dir,
/// tilde-expanded and deduplicated in order.
fn resolved_dirs(spec: &ChainSpec, state: &ChainState) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    for dir in &spec.dirs {
        push_unique(&mut out, expand_tilde(dir));
    }
    for seg in &state.segments {
        push_unique(&mut out, expand_tilde(&seg.segment.dir));
    }
    out
}

fn push_unique(out: &mut Vec<PathBuf>, path: PathBuf) {
    if !out.contains(&path) {
        out.push(path);
    }
}

/// Write every current segment's `<dir>/ROOT` (regenerated so a proofless
/// demotion / bisect rewrite is reflected).
fn write_all_roots(state: &ChainState) -> Result<(), CaptureChainError> {
    for seg in &state.segments {
        let dir = expand_tilde(&seg.segment.dir);
        ensure_dir(&dir)?;
        let root = dir.join("ROOT");
        std::fs::write(&root, segment_root_text(&seg.segment)).map_err(|source| {
            CaptureChainError::RootWrite {
                path: root.clone(),
                source,
            }
        })?;
    }
    Ok(())
}

fn build_inv(seg: &SegmentState, spec: &ChainSpec, dirs: &[PathBuf]) -> BuildInvocation {
    BuildInvocation {
        session: seg.segment.session.clone(),
        record_proofs: seg.segment.record_proofs,
        threads: seg.threads,
        isabelle_home: expand_tilde(&spec.isabelle_home),
        dirs: dirs.to_vec(),
    }
}

fn ensure_dir(dir: &Path) -> Result<(), CaptureChainError> {
    std::fs::create_dir_all(dir).map_err(|source| CaptureChainError::CreateDir {
        path: dir.to_path_buf(),
        source,
    })
}

fn append_log(log_path: &Path, text: &str) -> Result<(), CaptureChainError> {
    use std::io::Write as _;
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(log_path)
        .map_err(|source| CaptureChainError::LogWrite {
            path: log_path.to_path_buf(),
            source,
        })?;
    file.write_all(text.as_bytes())
        .map_err(|source| CaptureChainError::LogWrite {
            path: log_path.to_path_buf(),
            source,
        })
}

fn summarize(state: &ChainState, collected: usize) -> CaptureSummary {
    CaptureSummary {
        total_segments: state.segments.len(),
        ok: count_status(state, SegStatus::Ok),
        proofless: count_status(state, SegStatus::Proofless),
        failed: count_status(state, SegStatus::Failed),
        bisects: state.bisects,
        retries_threads1: state.retries_threads1,
        captures_collected: collected,
    }
}

fn count_status(state: &ChainState, want: SegStatus) -> usize {
    state.segments.iter().filter(|s| s.status == want).count()
}

/// Print the plan (and each generated ROOT) for `--dry`.
fn print_plan(spec: &ChainSpec, state: &ChainState, work_dir: &Path) {
    println!("capture-chain plan ({} segment(s)):", state.segments.len());
    println!(
        "  isabelle_home: {}",
        expand_tilde(&spec.isabelle_home).display()
    );
    println!("  work_dir:      {}", work_dir.display());
    println!("  threads:       {}", spec.threads);
    println!(
        "  collect:       {} → {}  (glob {})",
        expand_tilde(&spec.collect.from_dir).display(),
        expand_tilde(&spec.collect.to_dir).display(),
        spec.collect.glob
    );
    println!("  -d dirs:       {}", dirs_line(spec, state));
    for (idx, seg) in state.segments.iter().enumerate() {
        println!(
            "\n[{idx}] session={} parent={} status={:?} record_proofs={} threads={} theories={}",
            seg.segment.session,
            seg.segment.parent,
            seg.status,
            seg.segment.record_proofs,
            seg.threads,
            seg.segment.theories.len()
        );
        println!("     dir={}", expand_tilde(&seg.segment.dir).display());
        println!(
            "     ROOT:\n{}",
            indent(&segment_root_text(&seg.segment), "       ")
        );
    }
}

fn dirs_line(spec: &ChainSpec, state: &ChainState) -> String {
    resolved_dirs(spec, state)
        .iter()
        .map(|d| format!("-d {}", d.display()))
        .collect::<Vec<_>>()
        .join(" ")
}

fn indent(text: &str, prefix: &str) -> String {
    text.lines()
        .map(|l| format!("{prefix}{l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn now_unix_secs() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}
