//! Test-only local inference diagnostics, never declaration admission.
//!
//! Callers load serially and run on fresh LARGE_STACK threads without an
//! ambient deadline. Workers borrow that frozen environment, create a checker
//! per item, and never inherit a checker or its TLS work-meter account. An
//! ambient declaration budget keeps execution on the caller thread instead.

use super::error_category_str;
use clean_kernel::env::{ConstantInfo, Environment};
use clean_kernel::tc::{declaration_budget_limit, TypeChecker, TypeError};
use clean_kernel::test_utils::LARGE_STACK;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

const DISPLAY_SAMPLES: usize = 5;

#[derive(Debug, Default, PartialEq, Eq)]
struct ErrorCategory {
    // Every refusal is retained. Only the detailed display samples are capped.
    names: Vec<(usize, String)>,
    samples: Vec<(usize, String)>,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct TcResults {
    attempted: usize,
    ok: usize,
    failed: usize,
    errors: BTreeMap<String, ErrorCategory>,
    unknown_consts: BTreeMap<String, usize>,
    heartbeat_exceeded_names: Vec<(usize, String)>,
}

impl TcResults {
    fn record(&mut self, ordinal: usize, ci: &ConstantInfo, result: Result<(), TypeError>) {
        self.attempted += 1;
        match result {
            Ok(()) => self.ok += 1,
            Err(error) => {
                self.failed += 1;
                let name = ci.name.to_string();
                if matches!(&error, TypeError::HeartbeatExceeded { .. }) {
                    self.heartbeat_exceeded_names.push((ordinal, name.clone()));
                }
                if let TypeError::UnknownConst(missing) = &error {
                    *self.unknown_consts.entry(missing.to_string()).or_default() += 1;
                }
                let category = self.errors.entry(error_category_str(&error)).or_default();
                category.names.push((ordinal, name));
                if category.samples.len() < DISPLAY_SAMPLES {
                    category
                        .samples
                        .push((ordinal, format!("{}: {error:?}", ci.name)));
                }
            }
        }
    }

    fn merge(&mut self, other: Self) {
        self.attempted += other.attempted;
        self.ok += other.ok;
        self.failed += other.failed;
        for (name, count) in other.unknown_consts {
            *self.unknown_consts.entry(name).or_default() += count;
        }
        self.heartbeat_exceeded_names
            .extend(other.heartbeat_exceeded_names);
        for (name, category) in other.errors {
            let destination = self.errors.entry(name).or_default();
            destination.names.extend(category.names);
            destination.samples.extend(category.samples);
        }
    }

    fn finish(mut self, expected: usize) -> Self {
        self.heartbeat_exceeded_names.sort_by_key(|entry| entry.0);
        for category in self.errors.values_mut() {
            category.names.sort_by_key(|entry| entry.0);
            category.samples.sort_by_key(|entry| entry.0);
            category.samples.truncate(DISPLAY_SAMPLES);
        }
        assert_eq!(
            self.attempted, expected,
            "diagnostic dropped or repeated a roster item"
        );
        assert_eq!(
            self.ok + self.failed,
            expected,
            "diagnostic verdict accounting differs"
        );
        assert_eq!(
            self.errors
                .values()
                .map(|category| category.names.len())
                .sum::<usize>(),
            self.failed,
            "diagnostic omitted refusal names"
        );
        self
    }
}

#[derive(Clone, Copy)]
enum Part {
    Types,
    Values,
}

impl Part {
    fn label(self) -> &'static str {
        match self {
            Self::Types => "Types",
            Self::Values => "Values",
        }
    }

    fn roster(self, env: &Environment) -> Vec<&ConstantInfo> {
        let mut items: Vec<_> = env
            .constants()
            .filter(|ci| matches!(self, Self::Types) || ci.value.is_some())
            .collect();
        items.sort_by(|left, right| left.name.cmp(&right.name));
        items
    }

    fn heartbeat(self) -> Option<u32> {
        match self {
            // Preserve new(env)'s existing 2M default; no checker reuse.
            Self::Types => None,
            // Existing value diagnostics deliberately match Lean's unlimited
            // kernel behavior; parallelism must not change this policy.
            Self::Values => Some(0),
        }
    }
}

fn worker_count(requested: Option<&str>, available: usize, items: usize) -> usize {
    let requested = requested
        .and_then(|text| text.parse::<usize>().ok())
        .filter(|count| *count > 0)
        .unwrap_or(1);
    requested.min(available.max(1)).min(items)
}

fn admitted_workers(items: usize) -> usize {
    worker_count(
        std::env::var("CARGO_BUILD_JOBS").ok().as_deref(),
        std::thread::available_parallelism()
            .map(usize::from)
            .unwrap_or(1),
        items,
    )
}

fn checker(env: &Environment, heartbeat: Option<u32>) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(env);
    if let Some(limit) = heartbeat {
        tc.set_heartbeat_limit(limit);
    }
    tc
}

fn infer(
    env: &Environment,
    ci: &ConstantInfo,
    part: Part,
    heartbeat: Option<u32>,
) -> Result<(), TypeError> {
    let tc = checker(env, heartbeat);
    let expression = match part {
        Part::Types => &ci.type_,
        Part::Values => ci
            .value
            .as_ref()
            .expect("value roster contains only present values"),
    };
    tc.infer_type(expression).map(|_| ())
}

fn run_roster(
    items: &[&ConstantInfo],
    workers: usize,
    label: &str,
    check: impl Fn(&ConstantInfo) -> Result<(), TypeError> + Sync,
) -> TcResults {
    let workers = workers.max(1).min(items.len());
    if workers == 0 {
        return TcResults::default();
    }
    let start = Instant::now();
    // Thread-local budgets are not inherited. These callers install none,
    // but an explicitly scoped declaration budget must never disappear.
    if workers == 1 || declaration_budget_limit() != 0 {
        let mut results = TcResults::default();
        for (ordinal, ci) in items.iter().enumerate() {
            results.record(ordinal, ci, check(ci));
            if (ordinal + 1).is_multiple_of(5000) {
                eprintln!(
                    "  {label} progress: {}/{} ({:.1}s)...",
                    ordinal + 1,
                    items.len(),
                    start.elapsed().as_secs_f64()
                );
            }
        }
        return results.finish(items.len());
    }

    let next = AtomicUsize::new(0);
    let completed = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for worker in 0..workers {
            let next = &next;
            let completed = &completed;
            let check = &check;
            let start = &start;
            handles.push(
                std::thread::Builder::new()
                    .name(format!("ac1-{label}-{worker}"))
                    .stack_size(LARGE_STACK)
                    .spawn_scoped(scope, move || {
                        let mut results = TcResults::default();
                        loop {
                            let ordinal = next.fetch_add(1, Ordering::Relaxed);
                            let Some(ci) = items.get(ordinal) else { break };
                            results.record(ordinal, ci, check(ci));
                            let count = completed.fetch_add(1, Ordering::Relaxed) + 1;
                            if count.is_multiple_of(5000) {
                                eprintln!(
                                    "  {label} progress: {count}/{} ({:.1}s)...",
                                    items.len(),
                                    start.elapsed().as_secs_f64()
                                );
                            }
                        }
                        results
                    })
                    .expect("diagnostic worker creation failed"),
            );
        }
        let mut results = TcResults::default();
        for handle in handles {
            // Scope joins every worker even while unwinding. A worker's panic
            // is a failing test, never an absent or successful chunk.
            results.merge(
                handle
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
            );
        }
        results.finish(items.len())
    })
}

fn run(env: &Environment, part: Part) -> TcResults {
    let items = part.roster(env);
    run_roster(&items, admitted_workers(items.len()), part.label(), |ci| {
        infer(env, ci, part, part.heartbeat())
    })
}

pub(super) fn run_tc_on_types(env: &Environment) -> TcResults {
    run(env, Part::Types)
}

pub(super) fn run_tc_on_values(env: &Environment) -> TcResults {
    run(env, Part::Values)
}

pub(super) fn print_tc_results(label: &str, results: &TcResults) {
    let total = results.attempted;
    let rate = if total > 0 {
        results.ok as f64 / total as f64 * 100.0
    } else {
        0.0
    };
    println!(
        "\n  {label} TC: {}/{total} OK ({rate:.1}%), {} errors, {} heartbeat exceeded",
        results.ok,
        results.failed,
        results.heartbeat_exceeded_names.len()
    );
    if !results.errors.is_empty() {
        println!("\n  {label} errors by category:");
        for (category, errors) in &results.errors {
            println!("    {category}: {} errors", errors.names.len());
            for (_, sample) in errors.samples.iter().take(3) {
                println!("      {sample}");
            }
        }
    }
    if !results.unknown_consts.is_empty() {
        println!(
            "\n  {label} UnknownConst names ({} unique):",
            results.unknown_consts.len()
        );
        for (name, count) in &results.unknown_consts {
            println!("    {name}: {count} occurrences");
        }
    }
    if !results.heartbeat_exceeded_names.is_empty() {
        let mut namespaces = BTreeMap::<String, usize>::new();
        for (_, name) in &results.heartbeat_exceeded_names {
            *namespaces
                .entry(name.split('.').take(2).collect::<Vec<_>>().join("."))
                .or_default() += 1;
        }
        println!(
            "\n  {label} heartbeat exceeded by namespace ({} unique prefixes):",
            namespaces.len()
        );
        let mut sorted: Vec<_> = namespaces.into_iter().collect();
        sorted.sort_by_key(|entry| std::cmp::Reverse(entry.1));
        for (namespace, count) in sorted.iter().take(30) {
            println!("    {namespace}: {count}");
        }
        if sorted.len() > 30 {
            println!("    ... and {} more prefixes", sorted.len() - 30);
        }
        println!("\n  {label} first 20 heartbeat-exceeded names:");
        for (_, name) in results.heartbeat_exceeded_names.iter().take(20) {
            println!("    {name}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Expr, Level, Name};

    fn insert(env: &mut Environment, name: &str, ty: Expr, value: Option<Expr>) {
        env.add_constant_unchecked_for_test(ConstantInfo::new(
            Name::from_string(name),
            vec![],
            ty,
            value,
            false,
        ));
    }

    fn fixture() -> Environment {
        let mut env = Environment::default();
        // Reverse insertion order makes roster ordering independent of it.
        for index in (0..12).rev() {
            insert(
                &mut env,
                &format!("bad{index:02}"),
                Expr::const_(Name::from_string("missing"), vec![]),
                Some(Expr::const_(Name::from_string("missing"), vec![])),
            );
        }
        insert(
            &mut env,
            "good",
            Expr::sort(Level::zero()),
            Some(Expr::sort(Level::zero())),
        );
        insert(&mut env, "without_value", Expr::sort(Level::zero()), None);
        env
    }

    #[test]
    fn worker_budget_is_positive_conservative_and_bounded() {
        for input in [
            None,
            Some(""),
            Some("0"),
            Some("-1"),
            Some("bad"),
            Some("99999999999999999999999999"),
        ] {
            assert_eq!(worker_count(input, 8, 20), 1);
        }
        assert_eq!(worker_count(Some("8"), 3, 20), 3);
        assert_eq!(worker_count(Some("8"), 12, 2), 2);
        assert_eq!(worker_count(Some("8"), 0, 20), 1);
        assert_eq!(worker_count(Some("8"), 8, 0), 0);
    }

    #[test]
    fn workers_preserve_full_denominators_refusals_and_stable_samples() {
        let env = fixture();
        for part in [Part::Types, Part::Values] {
            let roster = part.roster(&env);
            let run = |workers| {
                run_roster(&roster, workers, "parity", |ci| {
                    infer(&env, ci, part, part.heartbeat())
                })
            };
            let serial = run(1);
            assert_eq!(serial, run(3));
            assert_eq!(serial.failed, 12);
            assert_eq!(
                serial.attempted,
                match part {
                    Part::Types => 14,
                    Part::Values => 13,
                }
            );
            let errors = &serial.errors["UnknownConst(missing)"];
            assert_eq!(errors.names.len(), 12);
            assert_eq!(errors.samples.len(), DISPLAY_SAMPLES);
            assert_eq!(errors.names[0].1, "bad00");
            assert_eq!(errors.samples[4].0, 4);
            assert_eq!(serial.unknown_consts["missing"], 12);
        }
    }

    #[test]
    fn value_roster_excludes_missing_values_and_checks_present_values_once() {
        let env = fixture();
        let roster = Part::Values.roster(&env);
        assert!(!roster
            .iter()
            .any(|ci| ci.name.to_string() == "without_value"));
        let counts: BTreeMap<_, _> = roster
            .iter()
            .map(|ci| (ci.name.clone(), AtomicUsize::new(0)))
            .collect();
        let results = run_roster(&roster, 3, "once", |ci| {
            counts[&ci.name].fetch_add(1, Ordering::Relaxed);
            infer(&env, ci, Part::Values, Part::Values.heartbeat())
        });
        assert_eq!(results.attempted, 13);
        assert!(counts
            .values()
            .all(|count| count.load(Ordering::Relaxed) == 1));
        assert_eq!(
            checker(&env, Part::Types.heartbeat()).heartbeat_limit(),
            2_000_000
        );
        assert_eq!(checker(&env, Part::Values.heartbeat()).heartbeat_limit(), 0);
    }

    #[test]
    fn fresh_checkers_keep_heartbeat_refusals_local_to_each_item() {
        let mut env = Environment::default();
        insert(
            &mut env,
            "a_exhausted",
            Expr::sort(Level::zero()),
            Some(Expr::sort(Level::zero())),
        );
        for index in 0..12 {
            insert(
                &mut env,
                &format!("b_good{index:02}"),
                Expr::sort(Level::zero()),
                Some(Expr::sort(Level::zero())),
            );
        }
        let roster = Part::Values.roster(&env);
        let run = |workers| {
            run_roster(&roster, workers, "budget", |ci| {
                if ci.name.to_string() == "a_exhausted" {
                    // The kernel's existing heartbeat control: one inference
                    // spends limit=1; the next inference must refuse. Do not
                    // assume how many ticks one nested expression consumes.
                    let starved = checker(&env, Some(1));
                    assert!(matches!(
                        starved.infer_type(&ci.type_)?.kind(),
                        clean_kernel::ExprKind::Sort(_)
                    ));
                    starved.infer_type(&ci.type_).map(|_| ())
                } else {
                    // Every subsequent item needs its OWN single heartbeat.
                    infer(&env, ci, Part::Values, Some(1))
                }
            })
        };
        let serial = run(1);
        assert_eq!(serial, run(3));
        assert_eq!(serial.attempted, 13);
        assert_eq!(serial.ok, 12);
        assert_eq!(serial.failed, 1);
        assert_eq!(
            serial.heartbeat_exceeded_names,
            vec![(0, "a_exhausted".into())]
        );
    }

    #[test]
    fn a_worker_panic_fails_the_diagnostic_instead_of_dropping_an_item() {
        let env = fixture();
        let roster = Part::Values.roster(&env);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_roster(&roster, 3, "panic", |ci| {
                assert_ne!(ci.name.to_string(), "bad05", "deliberate worker panic");
                Ok(())
            })
        }));
        assert!(result.is_err());
    }

    #[test]
    fn rejected_worker_creation_cannot_produce_a_partial_success() {
        let env = fixture();
        let roster = Part::Values.roster(&env);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // std::thread rejects an interior NUL in a native worker name.
            // Failed creation must propagate, never drop a roster chunk.
            run_roster(&roster, 3, "invalid\0worker", |_| Ok(()))
        }));
        assert!(result.is_err());
    }

    #[test]
    fn ambient_declaration_budget_is_not_lost_to_worker_threads() {
        struct Restore(u64);
        impl Drop for Restore {
            fn drop(&mut self) {
                clean_kernel::tc::set_declaration_budget(self.0);
            }
        }
        assert_eq!(
            declaration_budget_limit(),
            0,
            "fixture starts with no ambient budget"
        );
        let _restore = Restore(0);
        clean_kernel::tc::set_declaration_budget(1);
        let env = fixture();
        let roster = Part::Values.roster(&env);
        let caller = std::thread::current().id();
        let results = run_roster(&roster, 3, "ambient", |ci| {
            assert_eq!(std::thread::current().id(), caller);
            infer(&env, ci, Part::Values, Some(0))
        });
        assert!(results.failed > 0);
        assert!(results
            .errors
            .keys()
            .any(|category| category.contains("declaration")));
    }
}
