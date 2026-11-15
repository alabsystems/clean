// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! C4 diagnostic pilot. This refuses to call partial core events R2/R3 evidence.
use clean_kernel::env::Environment;
use clean_kernel::kcheck_trace::DomainClass;
use clean_olean::recheck_closed::reference_base::{
    reference_base_core_tracing, reference_base_progress, TraceObservation,
};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn class_name(class: &DomainClass) -> &'static str {
    match class {
        DomainClass::Identical => "identical",
        DomainClass::LevelInstantiated => "level_instantiation_only",
        DomainClass::Convertible { .. } => "convertible",
        DomainClass::Failed(_) => "failed",
        DomainClass::Missing(_) => "missing",
    }
}
fn table(counts: &BTreeMap<String, u64>) -> serde_json::Value {
    let total: u64 = counts.values().sum();
    let rows:Vec<_> = ["identical","level_instantiation_only","convertible","failed","missing"].into_iter().map(|class| {
        let count = counts.get(class).copied().unwrap_or(0);
        json!({"class":class,"count":count,"percent":if total==0 {None} else {Some(count as f64*100.0/total as f64)}})
    }).collect();
    json!({"total":total,"rows":rows})
}
fn distribution(mut ranked: Vec<(u64, String)>) -> serde_json::Value {
    ranked.sort();
    if ranked.is_empty() {
        return json!(null);
    }
    let n = ranked.len();
    json!({"complete_units":n,"total":ranked.iter().map(|(n,_)|*n).sum::<u64>(),"median":if n.is_multiple_of(2) {(ranked[n/2-1].0 as f64+ranked[n/2].0 as f64)/2.0}else{ranked[n/2].0 as f64},"p99_nearest_rank":ranked[(99*n).div_ceil(100)-1].0,"maximum":ranked[n-1].0,"largest_ten":ranked.iter().rev().take(10).map(|(n,name)|json!({"name":name,"tokens":n})).collect::<Vec<_>>()})
}

fn artifact_module<'a>(lib: &Path, label: &'a str) -> &'a str {
    if lib
        .join(label.replace('.', "/"))
        .with_extension("olean")
        .is_file()
    {
        label
    } else {
        label
            .strip_suffix("._server")
            .or_else(|| label.strip_suffix("._private"))
            .unwrap_or(label)
    }
}

#[derive(Default)]
struct TraceTotals {
    observed: BTreeSet<String>,
    row_count: usize,
    core_complete: usize,
    counts: BTreeMap<&'static str, u64>,
    spine_counts: BTreeMap<String, BTreeMap<String, u64>>,
    problems: Vec<serde_json::Value>,
    infer_ann_counts: BTreeMap<String, BTreeMap<String, u64>>,
    reductions: BTreeMap<String, u64>,
    minor_beta: BTreeMap<String, u64>,
    oracle_work: BTreeMap<String, BTreeMap<String, u64>>,
    compressed: Vec<(u64, String)>,
    uncompressed: Vec<(u64, String)>,
    conversion_cycles_cut: u64,
}

impl TraceTotals {
    fn new() -> Self {
        Self {
            counts: BTreeMap::from([
                ("identical_at_current_levels", 0),
                ("level_instantiation_only", 0),
                ("convertible", 0),
                ("failed", 0),
                ("missing", 0),
            ]),
            ..Self::default()
        }
    }

    fn observe(&mut self, row: &TraceObservation) {
        self.row_count += 1;
        self.observed.extend(row.members.iter().cloned());
        self.core_complete += usize::from(row.core_complete);
        self.conversion_cycles_cut += row.conversion_cycles_cut;
        for event in &row.beta {
            let name = match event {
                DomainClass::Identical => "identical_at_current_levels",
                DomainClass::LevelInstantiated => "level_instantiation_only",
                DomainClass::Convertible { .. } => "convertible",
                DomainClass::Failed(_) => "failed",
                DomainClass::Missing(_) => "missing",
            };
            *self.counts.entry(name).or_default() += 1;
        }
        for call in &row.oracle_conversions {
            let work = self.oracle_work.entry(call.source.clone()).or_default();
            *work.entry("calls".into()).or_default() += 1;
            *work.entry("heartbeats".into()).or_default() += call.heartbeats;
            let maximum = work.entry("maximum_heartbeats".into()).or_default();
            *maximum = (*maximum).max(call.heartbeats);
            *work
                .entry(
                    if call.budget_exhausted {
                        "undecided"
                    } else if call.equal {
                        "equal"
                    } else {
                        "unequal"
                    }
                    .into(),
                )
                .or_default() += 1;
            for (category, count) in &call.categories {
                *work.entry(format!("heartbeats/{category}")).or_default() += count;
            }
        }
        for event in &row.spines {
            let key = format!(
                "{}/{}/{}/{}",
                event.entry, event.family, event.target, event.position_kind
            );
            let class = class_name(&event.class);
            if event.target == "recursor" && event.position_kind == "major" {
                *self
                    .reductions
                    .entry(format!("{}/{}", event.entry, event.family))
                    .or_default() += 1;
            }
            *self
                .spine_counts
                .entry(key)
                .or_default()
                .entry(class.into())
                .or_default() += 1;
        }
        for (source, class) in &row.infer_ann_classes {
            *self
                .infer_ann_counts
                .entry(source.clone())
                .or_default()
                .entry(class_name(class).into())
                .or_default() += 1;
        }
        for problem in &row.domain_problems {
            self.problems
                .push(json!({"declaration":row.name,"problem":problem}));
        }
        for (kind, count) in &row.minor_beta {
            *self.minor_beta.entry(kind.clone()).or_default() += count;
        }
        if row.core_complete && row.reference_accepted {
            self.compressed
                .push((row.partial_tokens as u64, row.name.clone()));
            self.uncompressed
                .push((row.uncompressed_spine_tokens, row.name.clone()));
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let out = PathBuf::from(
        args.next()
            .ok_or("usage: kcheck_trace_experiment OUT [MODULE] [OPERATIONS]")?,
    );
    let module = args.next().unwrap_or_else(|| "Init".into());
    let operations = args
        .next()
        .map(|v| v.parse())
        .transpose()?
        .unwrap_or(100_000u64);
    if args.next().is_some() {
        return Err("unexpected argument".into());
    }
    let started = Instant::now();
    let lib = clean_olean::require_pinned_lean_lib_path()?;
    eprintln!("C4 pilot: loading {module} from {}", lib.display());
    let mut env = Environment::for_lean_replay();
    let summaries =
        clean_olean::load_module_with_deps(&mut env, &module, std::slice::from_ref(&lib))?;
    let mut targets: BTreeSet<_> = env
        .constants()
        .map(|c| c.name.clone())
        .chain(env.inductives().map(|i| i.name.clone()))
        .chain(env.constructors().map(|c| c.name.clone()))
        .chain(env.recursors().map(|r| r.name.clone()))
        .collect();
    let resident_names = targets.len();
    let mut artifact_names = BTreeSet::new();
    let mut modules = BTreeSet::new();
    let mut loader_refusals = Vec::new();
    for summary in &summaries {
        for skipped in &summary.skipped_constants {
            loader_refusals.push(
                json!({"name":skipped.name,"reason":skipped.reason,"source":"skipped_constant"}),
            );
        }
        for (name, reason) in summary
            .refused_completions
            .iter()
            .chain(&summary.shadowed_declarations)
        {
            loader_refusals.push(json!({"name":name.to_unambiguous_string(),"reason":reason,"source":"completion_or_shadow"}));
        }
        let label = summary.module_name.as_deref().ok_or("unnamed import")?;
        let artifact = artifact_module(&lib, label);
        if modules.insert(artifact.to_string()) {
            let path = lib.join(artifact.replace('.', "/")).with_extension("olean");
            clean_olean::toolchain_identity::pinned_toolchain_module(artifact, &path)?;
            artifact_names.extend(
                clean_olean::read_artifact(artifact, &path, clean_olean::ArtifactDepth::Names)?
                    .names,
            );
        }
    }
    targets.extend(artifact_names.iter().cloned());
    let names: BTreeSet<_> = targets.iter().map(|n| n.to_unambiguous_string()).collect();
    let options = ClosedRecheckOptions::default();
    eprintln!(
        "C4 pilot: ordinary fenced replay of {} constants",
        targets.len()
    );
    let baseline_started = Instant::now();
    let baseline_report = reference_base_progress(&env, &targets, &options)?;
    let baseline_ms = baseline_started.elapsed().as_millis();
    std::fs::create_dir_all(&out)?;
    std::fs::write(
        out.join("ordinary.json"),
        serde_json::to_vec_pretty(
            &json!({"report":baseline_report,"wall_ms":baseline_ms,"module":module,"library":lib}),
        )?,
    )?;
    eprintln!("C4 pilot: independent core observer, operation budget {operations}");
    let trace_started = Instant::now();
    let mut totals = TraceTotals::new();
    let trace_report = reference_base_core_tracing(
        &env,
        &targets,
        &options,
        operations,
        Some(&out.join("observations.jsonl")),
        &mut |row| totals.observe(row),
    )?;
    let trace_ms = trace_started.elapsed().as_millis();
    let TraceTotals {
        observed,
        row_count,
        core_complete,
        counts,
        spine_counts,
        problems,
        infer_ann_counts,
        reductions,
        minor_beta,
        oracle_work,
        compressed,
        uncompressed,
        conversion_cycles_cut,
    } = totals;
    let unobserved: Vec<_> = names.difference(&observed).cloned().collect();
    let events: u64 = counts.values().sum();
    let percentages: BTreeMap<_, _> = counts
        .iter()
        .map(|(k, v)| {
            (
                *k,
                if events == 0 {
                    None
                } else {
                    Some(*v as f64 * 100.0 / events as f64)
                },
            )
        })
        .collect();
    let compressed_distribution = distribution(compressed);
    let uncompressed_distribution = distribution(uncompressed);
    let spine_tables: BTreeMap<_, _> = spine_counts
        .iter()
        .map(|(key, counts)| (key, table(counts)))
        .collect();
    let infer_ann_tables: BTreeMap<_, _> = infer_ann_counts
        .iter()
        .map(|(key, counts)| (key, table(counts)))
        .collect();
    let complete = core_complete == row_count && unobserved.is_empty();
    let mut ordinary = serde_json::to_value(&baseline_report)?;
    let mut traced = serde_json::to_value(&trace_report)?;
    for value in [&mut ordinary, &mut traced] {
        if let Some(obj) = value.as_object_mut() {
            obj.remove("elapsed_ms");
        }
    }
    let same_verdicts = ordinary == traced;
    let revision = std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()?;
    if !revision.status.success() {
        return Err("git revision query failed".into());
    }
    let status = std::process::Command::new("git")
        .args(["status", "--porcelain"])
        .output()?;
    if !status.status.success() {
        return Err("git status query failed".into());
    }
    // Separate object sections keep serde_json's macro expansion below the
    // default compiler recursion limit; this does not change the report schema.
    let sections = [
        json!({
        "schema":4,"observation_storage":"streamed_jsonl","iota_rhs_semantics":"labelled_rule_spine_revision4","identity_convention":"canonical erasure equality, as REFL; full nested-label equality is not a separate class","status":"incomplete_core_pilot_not_R2_R3_evidence",
        "revision":String::from_utf8(revision.stdout)?.trim(),"dirty":!status.stdout.is_empty(),
        "module":module,"pinned_lean":include_str!("../../../../lean-toolchain").trim(),"library":lib,
        }),
        json!({
        "operation_budget_per_declaration":operations,"source_constants":targets.len(),
        "denominator":"union of resident constants/family members and raw authoritative artifact names; loader refusals separately named",
        "resident_names":resident_names,"raw_artifact_names":artifact_names.len(),"loader_refusals":loader_refusals,"modules":modules,
        "inductive_families":env.inductives().map(|family|(family.name.to_unambiguous_string(),family.name.to_string())).collect::<BTreeMap<_,_>>(),
        "ordinary_declarations_observed":row_count,"core_complete_declarations":core_complete,
        "unobserved_names":unobserved,"same_reference_verdicts":same_verdicts,
        }),
        json!({
        "diagnostic_beta_events":events,"diagnostic_beta_counts":counts,"diagnostic_beta_percentages":percentages,
        "R2":null,"R3":null,"advice_lengths":null,
        "trace_coverage_complete":complete,
        }),
        json!({
        "producer_conversion_cycles_cut":conversion_cycles_cut,
        "existing_kernel_conversion_work":oracle_work,
        "existing_kernel_conversion_work_unit":"actual kernel operation heartbeats: whnf/isDefEq/inferType/kernelWork; not contracted head steps",
        "diagnostic_spine_counts":spine_counts,"diagnostic_spine_tables":spine_tables,"infer_ann_tables":infer_ann_tables,"recursor_reductions":reductions,"domain_problems":problems,"minor_beta":minor_beta,
        "complete_prefix_unit_token_distribution":{"compressed_spines":compressed_distribution,"uncompressed_spines":uncompressed_distribution},
        "token_distribution_status":"diagnostic producer journal, not design advice; failed units excluded and named in observations.jsonl",
        }),
        json!({
        "ordinary_wall_ms":baseline_ms,"observing_wall_ms":trace_ms,
        "partial_observer_ratio":if baseline_ms==0 {None}else{Some(trace_ms as f64/baseline_ms as f64)},
        "total_wall_ms":started.elapsed().as_millis(),
        "limitations":[
            "No advice bytes emitted: journal order is not a replayable certificate; R2/R3 verdicts remain unset",
            "Labelled core extended with literal, projection, structure eta and general recursor handling beyond the design's slice",
            "Persistent syntax installed only after ordinary and tracing admission both succeed; reannotated dependencies are named holes",
            "Universe-only category uses pre-first-instantiation diagnostic syntax transported through term substitutions",
            "Producer head steps and certificate tokens remain separate from actual existing-kernel oracle heartbeats; every oracle checker/profiler is fresh, including its equation caches",
            "Depth and inference volume follow this producer's call structure, including extension and diagnostic work; they are not a native kcheck stack measurement",
            "Journal includes conversion search overhead; successful speculative branches may remain inside a successful outer branch",
            "All IOTA constructor walks are charged, including Prop; K constructor diagnostics have c=0; generic non-Eq K synthesis extends the slice and adds inference/depth work",
            "String literal expansion supports the pinned String.ofList layout; historical String.mk constructor expansion is a named coverage refusal",
            "Nat primitives are an explicit extension beyond the design Term: existing-kernel atomic folds charge CORE_L plus typed operand/spine certificates, and named stuck decisions preserve labelled applications; Nat.succ constructor labels are retained",
            "No MEMO tokens: equation and inference-result caches are disabled; active conversion-pair recursion guards cut failed search cycles and retain no answers",
            "Per-block inductive counts are atomic units rather than per-member advice lengths",
        ],
        "ordinary_report":baseline_report,"observing_report":trace_report,"observations":[],
        }),
    ];
    let mut fields = serde_json::Map::new();
    for section in sections {
        let serde_json::Value::Object(part) = section else {
            return Err("report section is not an object".into());
        };
        for (key, value) in part {
            if let serde_json::map::Entry::Vacant(entry) = fields.entry(key) {
                entry.insert(value);
            } else {
                return Err("duplicate report field".into());
            }
        }
    }
    let report = serde_json::Value::Object(fields);
    std::fs::create_dir_all(&out)?;
    std::fs::write(out.join("pilot.json"), serde_json::to_vec_pretty(&report)?)?;
    eprintln!("C4 incomplete pilot: {core_complete} complete core rows; {events} diagnostic beta events; same reference verdicts={same_verdicts}");
    if !same_verdicts {
        return Err("observer changed the ordinary reference report".into());
    }
    Ok(())
}
