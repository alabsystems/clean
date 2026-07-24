// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Kernel-parity batch sweep — the continue-on-error census harness.
//
// The graduation gate's fresh-env re-check exposes Lean-fidelity divergences
// ONE AT A TIME (fail-fast resolution; each serial rerun is ~35 min). This
// harness loads the candidates' olean closure ONCE, walks the v3.1 carry
// closure with the REAL intake machinery (`resolve_dependency` /
// `carry_inductive_family` — exact gate parity on the success path), and on
// each failure RECORDS the divergence then force-adds the source-imported
// constant (unchecked — diagnostic only, never a trust path) so the sweep
// continues PAST the failure. Output: the complete failure census in one
// batch, with taint tracking separating genuine first-divergences from
// cascade suspects.
//
// Heavy + env-gated (passes trivially when CLEAN_SWEEP_MODULES is unset):
//
//   CLEAN_SWEEP_MODULES=Crownproof.Basic,...               (csv)
//   CLEAN_SWEEP_SEARCH_PATHS=/path/a:/path/b               (colon-sep)
//   CLEAN_SWEEP_CANDIDATES=Crownproof.farkas_comb,...      (csv)
//   CLEAN_SWEEP_OUT=/tmp/sweep-out                         (census dir)
//   cargo test --locked --release -p clean-mathverse --lib \
//     graduate::tests::sweep_census -- --nocapture

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Write as _;
use std::path::PathBuf;

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{ConstantKind, Environment, Name};

use crate::graduate::intake::{collect_constant_refs, resolve_dependency, GateState, RecheckBase};
use crate::graduate::intake_family::{
    carry_inductive_family, consume_telescope_annotations, inductive_family_root,
};
use crate::graduate::shadow::shadow_exprs_equal;

/// One recorded divergence (or policy rejection) from the batch sweep.
#[derive(Debug)]
struct SweepFailure {
    name: String,
    kind: &'static str,
    genre: String,
    /// Failed constants in this constant's transitive dependency closure
    /// (empty = GENUINE first-divergence; non-empty = cascade suspect).
    tainted_by: Vec<String>,
    error: String,
}

/// Sweep state: the gate's real `GateState` plus continue-on-error
/// bookkeeping (visited memo with taint sets, failure census, counters).
struct SweepCx<'a> {
    source: &'a Environment,
    state: GateState,
    /// name -> failed names in its transitive closure (incl. itself).
    visited: HashMap<String, BTreeSet<String>>,
    stack: Vec<String>,
    failures: Vec<SweepFailure>,
    ok_by_kind: BTreeMap<&'static str, usize>,
    /// Names (family roots for members) whose shadow cross-check already ran.
    shadow_checked: std::collections::HashSet<String>,
}

impl<'a> SweepCx<'a> {
    fn new(source: &'a Environment, base: RecheckBase) -> Self {
        Self {
            source,
            state: GateState::new(base),
            visited: HashMap::new(),
            stack: Vec::new(),
            failures: Vec::new(),
            ok_by_kind: BTreeMap::new(),
            shadow_checked: std::collections::HashSet::new(),
        }
    }

    fn record(&mut self, name: &str, kind: &'static str, reason: String, taint: &TaintSet) {
        let genre = classify_genre(&reason);
        eprintln!(
            "[sweep] FAIL {kind} `{name}` genre={genre} tainted_by={} :: {}",
            taint.len(),
            reason.chars().take(220).collect::<String>()
        );
        self.failures.push(SweepFailure {
            name: name.to_string(),
            kind,
            genre,
            tainted_by: taint.iter().cloned().collect(),
            error: reason,
        });
    }

    fn count_ok(&mut self, kind: &'static str) {
        *self.ok_by_kind.entry(kind).or_insert(0) += 1;
    }

    /// Force-copy one constant (info + any inductive side-table entries)
    /// from the source environment into the recheck environment so the
    /// sweep can continue past a recorded failure.
    //
    // SOUNDNESS: diagnostic harness only (#[cfg(test)]; census output is
    // never a trust artifact) — the unchecked add deliberately installs
    // the Lean-validated source metadata so constants BEHIND a divergence
    // still get a genuine add_decl re-check.
    fn force_add_from_source(&mut self, name: &Name) {
        if let Some(ind) = self.source.get_inductive(name) {
            self.state.recheck.register_inductive(ind.clone());
        }
        if let Some(ctor) = self.source.get_constructor(name) {
            self.state.recheck.register_constructor(ctor.clone());
        }
        if let Some(rec) = self.source.get_recursor(name) {
            self.state.recheck.register_recursor(rec.clone());
        }
        if self.state.recheck.get_const(name).is_none() {
            if let Some(info) = self.source.get_const(name) {
                self.state
                    .recheck
                    .extend_constants_unchecked(std::iter::once(info.clone()));
            }
        }
    }
}

type TaintSet = BTreeSet<String>;

/// DFS post-order sweep of one dependency. Returns the taint set (failed
/// constants in the transitive closure, including `dep` itself when its
/// own re-check failed).
fn sweep_dep(cx: &mut SweepCx<'_>, dep: &str) -> TaintSet {
    if let Some(taint) = cx.visited.get(dep) {
        return taint.clone();
    }
    if cx.stack.iter().any(|n| n == dep) {
        // The gate would reject the whole chain; record once, fail open.
        let reason = format!(
            "dependency-cycle: `{dep}` participates in a reference cycle ({})",
            cx.stack.join(" -> ")
        );
        let taint = TaintSet::new();
        cx.record(dep, "cycle", reason, &taint);
        return TaintSet::from([dep.to_string()]);
    }
    let dep_name = Name::from_string(dep);
    if cx.state.recheck.get_const(&dep_name).is_some() {
        // Base (prelude/core), an already-carried item, or a force-added
        // fallback. The gate substitutes the recheck spelling SILENTLY — the
        // shadow cross-check records every case where that substitution is
        // not kernel-faithful (the Monoid-overlay / opaque-Nat.mod genre).
        // Items carried BY THIS RUN are run-derived, not silent base
        // substitution — the production guard exempts them via carried_idx,
        // and so does the census (their regenerated casesOn/recOn members
        // legitimately differ from the source's stored definition VALUES).
        if !cx.state.carried_idx.contains_key(dep) {
            shadow_check(cx, dep, &dep_name);
        }
        cx.visited.insert(dep.to_string(), TaintSet::new());
        return TaintSet::new();
    }

    // Inductive-family members sweep as one unit rooted at the family.
    // Value-bearing members the kernel-certificate replay does not
    // regenerate (Lean's casesOn/recOn definitions) fall through to the
    // ordinary definition path below, mirroring resolve_dependency.
    let value_bearing_member = inductive_family_root(cx.source, &dep_name).is_some()
        && cx
            .source
            .get_const(&dep_name)
            .is_some_and(|info| info.value.is_some());
    if let Some(root) =
        inductive_family_root(cx.source, &dep_name).filter(|_| !value_bearing_member)
    {
        let root_str = root.to_string();
        let taint = if root_str == dep {
            sweep_family_root(cx, &root)
        } else {
            sweep_dep(cx, &root_str)
        };
        let mut taint = taint;
        if cx.state.recheck.get_const(&dep_name).is_none() {
            if !taint.contains(&root_str) {
                // The family carried CLEAN yet its regeneration did not
                // produce this side-table member — a parity divergence in
                // its own right (the gate would reject the dependent with
                // `carried-inductive-failed: ... not regenerated`).
                cx.record(
                    dep,
                    "family-member",
                    format!(
                        "missing-regenerated-member: family `{root_str}` carried but \
                         member `{dep}` was not regenerated by add_inductive"
                    ),
                    &taint,
                );
                taint.insert(dep.to_string());
            }
            // Root failed (members fall back lazily) or the member is
            // missing from the regeneration: continue past it.
            cx.force_add_from_source(&dep_name);
        }
        cx.visited.insert(dep.to_string(), taint.clone());
        return taint;
    }

    let Some(info) = cx.source.get_const(&dep_name) else {
        let taint = TaintSet::new();
        cx.record(
            dep,
            "unknown",
            format!(
                "unknown-constant: `{dep}` is neither in the prelude nor the source environment"
            ),
            &taint,
        );
        let taint = TaintSet::from([dep.to_string()]);
        cx.visited.insert(dep.to_string(), taint.clone());
        return taint;
    };
    let kind = match info.kind {
        ConstantKind::Definition => "definition",
        ConstantKind::Theorem => "theorem",
        ConstantKind::Axiom => "axiom",
        ConstantKind::Opaque => "opaque",
    };

    // Resolve the constant's own references first (continue-on-error).
    let mut refs: BTreeSet<String> = collect_constant_refs(&info.type_).into_iter().collect();
    if let Some(value) = &info.value {
        refs.extend(collect_constant_refs(value));
    }
    let mut taint = TaintSet::new();
    cx.stack.push(dep.to_string());
    for r in &refs {
        taint.extend(sweep_dep(cx, r));
    }
    cx.stack.pop();

    // Single-shot REAL intake resolution: every inner ref is now present,
    // so this performs exactly the gate's own carry (add_decl with value,
    // dependency order) for this one constant.
    clean_kernel::reduction_stats_reset();
    let resolve_started = std::time::Instant::now();
    match resolve_dependency(cx.source, &mut cx.state, dep, &mut Vec::new()) {
        Ok(()) => {
            cx.count_ok(kind);
            let elapsed = resolve_started.elapsed();
            if elapsed.as_secs_f64() > 1.0 {
                eprintln!(
                    "[sweep] SLOW OK {kind} `{dep}` took {:.2}s",
                    elapsed.as_secs_f64()
                );
                let stats = clean_kernel::reduction_stats_report(20);
                if !stats.is_empty() {
                    eprintln!("[sweep] reduction stats for `{dep}`:\n{stats}");
                }
            }
        }
        Err(reason) => {
            let stats = clean_kernel::reduction_stats_report(20);
            if !stats.is_empty() {
                eprintln!(
                    "[sweep] reduction stats for FAILED `{dep}` ({:.2}s):\n{stats}",
                    resolve_started.elapsed().as_secs_f64()
                );
            }
            cx.record(dep, kind, reason, &taint);
            cx.force_add_from_source(&dep_name);
            taint.insert(dep.to_string());
        }
    }
    cx.visited.insert(dep.to_string(), taint.clone());
    taint
}

/// Sweep one inductive-family root: pre-resolve the (annotation-erased)
/// family refs continue-on-error, then run the gate's real
/// `carry_inductive_family` single-shot.
fn sweep_family_root(cx: &mut SweepCx<'_>, root: &Name) -> TaintSet {
    let root_str = root.to_string();
    let mut taint = TaintSet::new();
    if let Some(mut decl) = cx.source.inductive_decl_of(root) {
        let mut member_set: BTreeSet<String> = BTreeSet::new();
        let mut refs: BTreeSet<String> = BTreeSet::new();
        for ty in &mut decl.types {
            ty.type_ = consume_telescope_annotations(&ty.type_);
            member_set.insert(ty.name.to_string());
            refs.extend(collect_constant_refs(&ty.type_));
            for ctor in &mut ty.constructors {
                ctor.type_ = consume_telescope_annotations(&ctor.type_);
                member_set.insert(ctor.name.to_string());
                refs.extend(collect_constant_refs(&ctor.type_));
            }
        }
        cx.stack.push(root_str.clone());
        for r in refs.difference(&member_set) {
            taint.extend(sweep_dep(cx, r));
        }
        cx.stack.pop();
    }
    match carry_inductive_family(cx.source, &mut cx.state, root, &mut Vec::new()) {
        Ok(()) => {
            cx.count_ok("inductive-family");
        }
        Err(reason) => {
            cx.record(&root_str, "inductive-family", reason, &taint);
            taint.insert(root_str.clone());
            // Fall back to the Lean-validated source members: the root
            // and constructors now; recursor-kind members lazily when a
            // later dependent references them.
            cx.force_add_from_source(root);
            if let Some(ind) = cx.source.get_inductive(root) {
                for ctor in ind.constructor_names.clone() {
                    cx.force_add_from_source(&ctor);
                }
            }
        }
    }
    cx.visited.insert(root_str, taint.clone());
    taint
}

fn run_sweep(
    modules: &[String],
    search_paths: &[PathBuf],
    candidates: &[String],
    out_dir: &PathBuf,
) {
    let mut source = Environment::default();
    for module in modules {
        let started = std::time::Instant::now();
        eprintln!("[sweep] loading {module} ...");
        let summaries = clean_olean::load_module_with_deps(&mut source, module, search_paths)
            .unwrap_or_else(|e| panic!("loading module `{module}`: {e}"));
        let added: usize = summaries.iter().map(|s| s.added_constants).sum();
        eprintln!(
            "[sweep] {module}: added={added} (env total {}) [{:.1}s]",
            source.constants().count(),
            started.elapsed().as_secs_f64()
        );
    }

    // CLEAN_SWEEP_BASE=core: the production v3.2 shadow-free Lean-core base
    // (the .olean-lane gate base); default: the Clean prelude.
    let base = if std::env::var("CLEAN_SWEEP_BASE").as_deref() == Ok("core") {
        RecheckBase::LeanCore
    } else {
        RecheckBase::CleanPrelude
    };
    eprintln!("[sweep] recheck base: {}", base.record_label());
    let mut cx = SweepCx::new(&source, base);
    // CLEAN_SWEEP_PROFILE=1: enable the kernel's per-name heartbeat profiler
    // for every recheck add_decl (the profile is embedded in any
    // HeartbeatExceeded error recorded by the census).
    if std::env::var("CLEAN_SWEEP_PROFILE").as_deref() == Ok("1") {
        cx.state
            .recheck
            .set_option("profileHeartbeats".to_string(), Some("true".to_string()));
    }
    // CLEAN_SWEEP_MAX_HEARTBEATS=<n>: override the recheck heartbeat budget
    // (0 = unlimited) for blowup diagnosis.
    if let Ok(limit) = std::env::var("CLEAN_SWEEP_MAX_HEARTBEATS") {
        cx.state
            .recheck
            .set_option("maxHeartbeats".to_string(), Some(limit));
    }
    let sweep_started = std::time::Instant::now();
    for cand in candidates {
        eprintln!("[sweep] === candidate {cand} ===");
        let taint = sweep_dep(&mut cx, cand);
        let verdict = if taint.is_empty() { "OK" } else { "TAINTED" };
        eprintln!(
            "[sweep] === candidate {cand}: {verdict} ({} failed in closure) ===",
            taint.len()
        );
        if !taint.is_empty() {
            eprintln!(
                "[sweep]     tainted_by: {}",
                taint.iter().cloned().collect::<Vec<_>>().join(", ")
            );
        }
    }
    eprintln!(
        "[sweep] sweep walk complete in {:.1}s",
        sweep_started.elapsed().as_secs_f64()
    );

    // ------------------------------------------------------------------
    // Census output
    // ------------------------------------------------------------------
    std::fs::create_dir_all(out_dir).expect("create census out dir");
    let jsonl_path = out_dir.join("census.jsonl");
    let mut jsonl = std::fs::File::create(&jsonl_path).expect("create census.jsonl");
    for f in &cx.failures {
        let line = serde_json::json!({
            "name": f.name,
            "kind": f.kind,
            "genre": f.genre,
            "genuine": f.tainted_by.is_empty(),
            "tainted_by": f.tainted_by,
            "error": f.error,
        });
        writeln!(jsonl, "{line}").expect("write census.jsonl line");
    }

    let mut summary = String::new();
    summary.push_str(&format!(
        "KERNEL-PARITY BATCH SWEEP CENSUS\nconstants re-checked OK: {:?}\nfailures: {}\n\n",
        cx.ok_by_kind,
        cx.failures.len()
    ));
    let mut by_genre: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for f in &cx.failures {
        let slot = by_genre.entry(f.genre.as_str()).or_insert((0, 0));
        if f.tainted_by.is_empty() {
            slot.0 += 1;
        } else {
            slot.1 += 1;
        }
    }
    summary.push_str("genre                                    genuine  cascade-suspect\n");
    for (genre, (genuine, cascade)) in &by_genre {
        summary.push_str(&format!("{genre:<40} {genuine:>7}  {cascade:>15}\n"));
    }
    summary.push_str("\nGENUINE first-divergences:\n");
    for f in cx.failures.iter().filter(|f| f.tainted_by.is_empty()) {
        summary.push_str(&format!(
            "  [{}] {} ({}): {}\n",
            f.genre,
            f.name,
            f.kind,
            f.error.chars().take(300).collect::<String>()
        ));
    }
    summary.push_str("\nCascade suspects (first 40):\n");
    for f in cx
        .failures
        .iter()
        .filter(|f| !f.tainted_by.is_empty())
        .take(40)
    {
        summary.push_str(&format!(
            "  [{}] {} ({}) tainted_by {:?}\n",
            f.genre,
            f.name,
            f.kind,
            f.tainted_by.iter().take(6).collect::<Vec<_>>()
        ));
    }
    let summary_path = out_dir.join("census-summary.txt");
    std::fs::write(&summary_path, &summary).expect("write census summary");
    println!("{summary}");
    println!(
        "[sweep] census written: {} + {}",
        jsonl_path.display(),
        summary_path.display()
    );

    // Optional per-constant diagnostics: CLEAN_SWEEP_DUMP=name1,name2 prints
    // source vs recheck spellings + inductive side-table stats.
    if let Ok(dump) = std::env::var("CLEAN_SWEEP_DUMP") {
        for name in dump.split(',').filter(|n| !n.is_empty()) {
            dump_constant(&source, &cx.state.recheck, name);
        }
    }
}

/// Env-gated heavy census run; trivially green when unconfigured.
#[test]
fn kernel_parity_batch_sweep_census() {
    let Ok(modules) = std::env::var("CLEAN_SWEEP_MODULES") else {
        eprintln!("kernel_parity_batch_sweep_census: skipped (CLEAN_SWEEP_MODULES unset)");
        return;
    };
    let search = std::env::var("CLEAN_SWEEP_SEARCH_PATHS")
        .expect("CLEAN_SWEEP_SEARCH_PATHS required with CLEAN_SWEEP_MODULES");
    let candidates = std::env::var("CLEAN_SWEEP_CANDIDATES")
        .expect("CLEAN_SWEEP_CANDIDATES required with CLEAN_SWEEP_MODULES");
    let out_dir = PathBuf::from(
        std::env::var("CLEAN_SWEEP_OUT").unwrap_or_else(|_| "/tmp/kernel-parity-sweep".to_string()),
    );

    let modules: Vec<String> = modules.split(',').map(str::to_string).collect();
    let search_paths: Vec<PathBuf> = search.split(':').map(PathBuf::from).collect();
    let candidates: Vec<String> = candidates.split(',').map(str::to_string).collect();

    // Mathlib-scale closures recurse deep — same 1 GiB worker-thread
    // discipline as `cmd_graduate`.
    const SWEEP_STACK_BYTES: usize = 1024 * 1024 * 1024;
    std::thread::Builder::new()
        .name("kernel-parity-sweep".to_string())
        .stack_size(SWEEP_STACK_BYTES)
        .spawn(move || run_sweep(&modules, &search_paths, &candidates, &out_dir))
        .expect("spawn sweep worker")
        .join()
        .expect("sweep worker panicked");
}

include!("sweep_census_support.rs");
