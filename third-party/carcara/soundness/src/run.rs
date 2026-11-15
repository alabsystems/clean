// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Battery orchestration and per-rule statistics.

use crate::gen;
use crate::model::Rng;
use crate::mutate;
use crate::oracle::{Cex, Instance, OracleConfig, Outcome};
use crate::seeds::{self, Seed};
use crate::worker::{Reply, Worker};
use std::collections::{BTreeMap, HashSet};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::Instant;

#[derive(Clone)]
pub struct BatteryConfig {
    pub mutants_per_seed: usize,
    pub max_rounds: usize,
    pub seed: u64,
    pub threads: usize,
    pub rule_filter: Option<Vec<String>>,
    pub generators: bool,
    pub max_examples: usize,
    pub oracle: OracleConfig,
    /// The `carcara-soundness` executable that serves `--worker` (defaults to the running one).
    pub worker_exe: Option<std::path::PathBuf>,
}

impl Default for BatteryConfig {
    fn default() -> Self {
        BatteryConfig {
            mutants_per_seed: 200,
            max_rounds: 3,
            seed: 1,
            threads: 6,
            rule_filter: None,
            generators: true,
            max_examples: 3,
            oracle: OracleConfig::default(),
            worker_exe: None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Example {
    pub source: String,
    pub instance: Instance,
    pub cex: Cex,
}

#[derive(Clone, Debug, Default)]
pub struct RuleStats {
    /// Accepted step occurrences (after de-duplicating instances).
    pub accepted: u64,
    /// Accepted steps for which some model made every hypothesis true.
    pub exercised: u64,
    pub counterexamples: u64,
    pub examples: Vec<Example>,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub seeds: usize,
    pub seed_expectation_mismatches: Vec<String>,
    pub instances_checked: u64,
    pub parse_errors: u64,
    pub panics: u64,
    pub panic_examples: Vec<(String, Instance, String)>,
    pub slow: Vec<(f64, String, String)>,
    pub rules: BTreeMap<String, RuleStats>,
    pub seconds: f64,
}

struct Shared {
    report: Mutex<Report>,
    max_examples: usize,
}

fn record(shared: &Shared, source: &str, inst: &Instance, outcome: &Outcome) {
    let mut r = shared.report.lock().unwrap();
    r.instances_checked += 1;
    if outcome.parse_error.is_some() {
        r.parse_errors += 1;
        return;
    }
    if let Some(p) = &outcome.panic {
        r.panics += 1;
        if r.panic_examples.len() < 40 {
            r.panic_examples
                .push((source.to_owned(), inst.clone(), p.clone()));
        }
        return;
    }
    let cex_steps: HashSet<(&str, bool)> = outcome
        .cexs
        .iter()
        .map(|c| (c.step.as_str(), c.global))
        .collect();
    let _ = cex_steps;
    for (step, rule) in &outcome.accepted {
        let st = r.rules.entry(rule.clone()).or_default();
        st.accepted += 1;
        if outcome.exercised.contains(step) {
            st.exercised += 1;
        }
    }
    for cex in &outcome.cexs {
        let st = r.rules.entry(cex.rule.clone()).or_default();
        st.counterexamples += 1;
        if st.examples.len() < shared.max_examples {
            st.examples.push(Example {
                source: source.to_owned(),
                instance: inst.clone(),
                cex: cex.clone(),
            });
        }
    }
}

fn seed_rules(seed: &Seed) -> Vec<String> {
    let mut rules = Vec::new();
    let mut rest = seed.proof.as_str();
    while let Some(k) = rest.find(":rule") {
        rest = &rest[k + 5..];
        let name: String = rest
            .trim_start()
            .chars()
            .take_while(|c| !c.is_whitespace() && *c != ')')
            .collect();
        rules.push(name);
    }
    rules
}

pub fn run_battery(tests_dir: &Path, cfg: &BatteryConfig) -> Report {
    let start = Instant::now();
    let mut all_seeds = seeds::harvest_dir(tests_dir);
    if let Some(filter) = &cfg.rule_filter {
        all_seeds.retain(|s| seed_rules(s).iter().any(|r| filter.contains(r)));
    }
    let mut work: Vec<(String, Instance, bool, Option<bool>)> = all_seeds
        .iter()
        .map(|s| {
            (
                format!("{}::{} [{}]", s.file, s.test, s.group),
                Instance {
                    defs: s.defs.clone(),
                    proof: s.proof.clone(),
                },
                true,
                Some(s.expected),
            )
        })
        .collect();
    for (family, inst) in gen::mutation_seeds() {
        work.push((format!("gen-seed::{}", family), inst, true, None));
    }
    if cfg.generators {
        for (family, inst) in gen::all(cfg.seed) {
            if let Some(filter) = &cfg.rule_filter {
                if !filter
                    .iter()
                    .any(|r| inst.proof.contains(&format!(":rule {}", r)))
                {
                    continue;
                }
            }
            work.push((format!("gen::{}", family), inst, false, None));
        }
    }
    let shared = Arc::new(Shared {
        report: Mutex::new(Report {
            seeds: all_seeds.len(),
            ..Default::default()
        }),
        max_examples: cfg.max_examples,
    });
    let work = Arc::new(work);
    let next = Arc::new(Mutex::new(0usize));
    let mut handles = Vec::new();
    for t in 0..cfg.threads.max(1) {
        let (work, next, shared, cfg) = (work.clone(), next.clone(), shared.clone(), cfg.clone());
        handles.push(std::thread::spawn(move || {
            let mut seen: HashSet<u64> = HashSet::new();
            let exe = cfg.worker_exe.clone();
            let mut worker = Worker::spawn(&cfg.oracle, exe.as_deref()).expect("spawn worker");
            let mut check = |inst: &Instance| -> Outcome {
                match worker.check(inst) {
                    Reply::Done(o) => o,
                    Reply::Crashed(status) => {
                        worker =
                            Worker::spawn(&cfg.oracle, exe.as_deref()).expect("respawn worker");
                        Outcome {
                            panic: Some(format!("process crashed: {}", status)),
                            ..Default::default()
                        }
                    }
                }
            };
            loop {
                let idx = {
                    let mut n = next.lock().unwrap();
                    if *n >= work.len() {
                        break;
                    }
                    *n += 1;
                    *n - 1
                };
                let (source, inst, mutate_it, expected) = &work[idx];
                let mut rng =
                    Rng::new(cfg.seed.wrapping_mul(1_000_003) ^ (idx as u64) ^ ((t as u64) << 48));
                let t0 = Instant::now();
                let outcome = check(inst);
                let dt = t0.elapsed().as_secs_f64();
                if dt > 0.5 {
                    shared.report.lock().unwrap().slow.push((
                        dt,
                        source.clone(),
                        inst.proof.chars().take(300).collect(),
                    ));
                }
                if let Some(exp) = expected {
                    let got = outcome.parse_error.is_none()
                        && outcome.panic.is_none()
                        && outcome.first_error.is_none();
                    if got != *exp {
                        shared
                            .report
                            .lock()
                            .unwrap()
                            .seed_expectation_mismatches
                            .push(format!(
                                "{}: expected {} got {} ({:?})",
                                source, exp, got, outcome.first_error
                            ));
                    }
                }
                record(&shared, source, inst, &outcome);
                if !*mutate_it {
                    continue;
                }
                for _ in 0..cfg.mutants_per_seed {
                    let Some(m) = mutate::mutate(inst, &mut rng, cfg.max_rounds, true) else {
                        continue;
                    };
                    let h = hash_instance(&m);
                    if !seen.insert(h) {
                        continue;
                    }
                    if std::env::var_os("CARCARA_SOUNDNESS_TRACE").is_some() {
                        eprintln!("--- {} (mutant)\n{}\n{}", source, m.defs, m.proof);
                    }
                    let outcome = check(&m);
                    record(&shared, &format!("{} (mutant)", source), &m, &outcome);
                }
            }
        }));
    }
    for h in handles {
        let _ = h.join();
    }
    let mut report = shared.report.lock().unwrap().clone();
    if cfg.generators {
        report.rules.insert(
            crate::literals::RULE.to_owned(),
            crate::literals::audit(cfg.max_examples),
        );
        report.rules.insert(
            crate::zero_extend::RULE.to_owned(),
            crate::zero_extend::audit(cfg.max_examples),
        );
    }
    report.seconds = start.elapsed().as_secs_f64();
    report
}

fn hash_instance(i: &Instance) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in i.defs.bytes().chain([0u8]).chain(i.proof.bytes()) {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01B3);
    }
    h
}

pub fn render(report: &Report) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "seeds {} | instances checked {} | parse errors {} | checker panics {} | {:.1}s\n",
        report.seeds, report.instances_checked, report.parse_errors, report.panics, report.seconds
    ));
    if !report.seed_expectation_mismatches.is_empty() {
        out.push_str(&format!(
            "seed expectation mismatches: {}\n",
            report.seed_expectation_mismatches.len()
        ));
        for m in report.seed_expectation_mismatches.iter() {
            out.push_str(&format!("  {}\n", m));
        }
    }
    out.push_str(&format!(
        "{:32} {:>10} {:>10} {:>8}\n",
        "rule", "accepted", "exercised", "UNSOUND"
    ));
    for (rule, st) in &report.rules {
        out.push_str(&format!(
            "{:32} {:>10} {:>10} {:>8}\n",
            rule, st.accepted, st.exercised, st.counterexamples
        ));
    }
    for (rule, st) in &report.rules {
        for ex in &st.examples {
            out.push_str(&format!(
                "\n=== UNSOUND {} ({} judgement) step {} from {}\n  model: {}\n--- definitions\n{}\n--- proof\n{}\n",
                rule,
                if ex.cex.global { "global" } else { "local" },
                ex.cex.step,
                ex.source,
                ex.cex.model,
                ex.instance.defs.trim(),
                ex.instance.proof.trim()
            ));
        }
    }
    let mut slow = report.slow.clone();
    slow.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    for (dt, src, text) in slow.iter().take(10) {
        out.push_str(&format!(
            "slow {:.1}s {} :: {}\n",
            dt,
            src,
            text.replace('\n', " ")
        ));
    }
    if !report.panic_examples.is_empty() {
        out.push_str("\n=== checker panics (robustness, not soundness)\n");
        let mut seen = HashSet::new();
        for (src, inst, msg) in &report.panic_examples {
            if seen.insert(msg.clone()) {
                out.push_str(&format!("--- {} :: {}\n{}\n", src, msg, inst.proof.trim()));
            }
        }
    }
    out
}
