// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Measure the dependency-closed re-check against a real `.olean` closure.
//!
//! ```text
//! measure_recheck_closed --root <Module> [--search <dir>]... \
//!     [--base default|lean-replay|import-prelude] \
//!     [--world <Lean-version>] \
//!     [--target <Const.Name>]... [--all-theorems-of <Module>] [--max-targets N] \
//!     [--dump-refusals <file>] [--print-extension-bindings]
//! ```
//!
//! `--base` picks the environment the closure is loaded ON TOP OF, and so the
//! environment every fingerprint is taken over: `default` (the historical
//! `Environment::default()`), `lean-replay` (`Environment::for_lean_replay`,
//! what the `.olean` re-check lanes start from) or `import-prelude`
//! (`Environment::try_with_prelude_for_import`, the base `clean check
//! --imports-prefer-olean` snapshots for its `ImportedConeGate`). A key the
//! base itself declares keeps the base's declaration (the loader keeps the
//! first declaration of a name), and its fingerprint is the base's.
//!
//! `--dump-refusals` writes EVERY refusal, one `subject<TAB>Debug` line each, so a run's
//! refusals can be classified in full rather than from the first 25.
//! `--print-extension-bindings` prints, after the replay, the
//! dependency-closed fingerprint of every extension key the cone declares, in
//! the form `recheck_closed/extension_binding.rs` pins them. The replay itself
//! always gates against the PINNED table; a library caller cannot choose
//! another.
//!
//! Prints, for the same environment and the same target set:
//!
//! * the LOCAL assumed-environment check (`typecheck_constants_full`) — the
//!   check lanes have been calling "a full kernel re-check";
//! * the DEPENDENCY-CLOSED replay (`recheck_closed`);
//!
//! with wall time, peak RSS, the cone size, and a refusal histogram. The point
//! of running both is the delta: they answer different questions about the same
//! bytes.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::LeanWorld;
use clean_olean::import::{load_module_with_deps, parse_module_file, ImportError};
use clean_olean::recheck_closed::{recheck_closed, ClosedRecheckOptions, RecheckLevel};
use clean_olean::verify_batch_full::typecheck_constants_full;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::time::Instant;

const HEARTBEATS: u32 = 2_000_000;

fn peak_rss_bytes() -> u64 {
    #[cfg(target_os = "macos")]
    {
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        // SAFETY: `usage` is a valid, fully initialized `rusage` and
        // `getrusage` only writes into it.
        if unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) } == 0 {
            // macOS reports ru_maxrss in BYTES.
            return usage.ru_maxrss as u64;
        }
    }
    #[cfg(target_os = "linux")]
    {
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        // SAFETY: as above.
        if unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) } == 0 {
            // Linux reports ru_maxrss in KILOBYTES.
            return (usage.ru_maxrss as u64) * 1024;
        }
    }
    0
}

struct Args {
    root: String,
    base: String,
    world: Option<LeanWorld>,
    search: Vec<PathBuf>,
    targets: Vec<String>,
    all_theorems_of: Option<String>,
    all_env_constants: bool,
    max_targets: Option<usize>,
    dump_refusals: Option<PathBuf>,
    print_extension_bindings: bool,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "Init".to_string(),
        base: "default".to_string(),
        world: None,
        search: Vec::new(),
        targets: Vec::new(),
        all_theorems_of: None,
        all_env_constants: false,
        max_targets: None,
        dump_refusals: None,
        print_extension_bindings: false,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root needs a value"),
            "--base" => args.base = it.next().expect("--base needs a value"),
            "--world" => {
                args.world = Some(
                    it.next()
                        .expect("--world needs a value")
                        .parse()
                        .expect("--world must name a supported Lean world"),
                );
            }
            "--search" => args
                .search
                .push(PathBuf::from(it.next().expect("--search needs a value"))),
            "--target" => args
                .targets
                .push(it.next().expect("--target needs a value")),
            "--all-theorems-of" => {
                args.all_theorems_of = Some(it.next().expect("--all-theorems-of needs a value"));
            }
            "--all-env-constants" => args.all_env_constants = true,
            "--max-targets" => {
                args.max_targets = Some(
                    it.next()
                        .expect("--max-targets needs a value")
                        .parse()
                        .expect("--max-targets must be a number"),
                );
            }
            "--dump-refusals" => {
                args.dump_refusals = Some(PathBuf::from(
                    it.next().expect("--dump-refusals needs a value"),
                ));
            }
            "--print-extension-bindings" => args.print_extension_bindings = true,
            other => panic!("unknown flag {other}"),
        }
    }
    args
}

/// Every constant a module's own `.olean` declares, in file order.
fn module_declared(search: &[PathBuf], module: &str) -> Vec<String> {
    let rel = module.replace('.', "/") + ".olean";
    for dir in search {
        let path = dir.join(&rel);
        if path.exists() {
            let parsed = parse_module_file(&path).expect("module must parse");
            return parsed.const_names;
        }
    }
    panic!("module {module} not found under {search:?}");
}

fn main() {
    let args = parse_args();
    println!("== measure_recheck_closed ==");
    println!("root       : {}", args.root);
    println!("search     : {:?}", args.search);
    println!("base       : {}", args.base);
    println!("world      : {:?}", args.world);

    let load_started = Instant::now();
    let mut env = match args.base.as_str() {
        "default" => Environment::default(),
        "lean-replay" => Environment::for_lean_replay(),
        "import-prelude" => {
            Environment::try_with_prelude_for_import().expect("the import-mode prelude must build")
        }
        other => panic!("unknown --base {other} (default | lean-replay | import-prelude)"),
    };
    if let Some(world) = args.world {
        clean_olean::declare_environment_world(&mut env, world.tag())
            .expect("the explicit world must agree with the chosen base");
    }
    let summaries: Result<Vec<_>, ImportError> =
        load_module_with_deps(&mut env, &args.root, &args.search);
    let summaries = summaries.expect("closure must load");
    let load_ms = load_started.elapsed().as_millis();
    let added: usize = summaries.iter().map(|s| s.added_constants).sum();
    let skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();
    let non_codegen: Vec<_> = summaries
        .iter()
        .flat_map(|s| s.skipped_constants.iter())
        .filter(|s| !s.reason.contains("compiler/code-generator artifact"))
        .collect();
    println!("load_ms    : {load_ms}");
    println!("modules    : {}", summaries.len());
    println!("added      : {added}");
    println!("skipped    : {skipped} (non-codegen {})", non_codegen.len());
    for s in non_codegen.iter().take(20) {
        println!("  SKIP {}: {}", s.name, s.reason);
    }
    println!("env consts : {}", env.constants().count());

    // A display string is not a name: `Name`'s `Display` does not escape a
    // component containing `.`, so re-interning a rendered name can name a
    // different constant. Resolve every string the user or an `.olean` module
    // gives us to the environment's OWN names; a string no constant renders to
    // is interned as-is, so the replay reports it absent rather than dropping it.
    let mut by_display: BTreeMap<String, Vec<Name>> = BTreeMap::new();
    for c in env.constants() {
        by_display
            .entry(c.name.to_string())
            .or_default()
            .push(c.name.clone());
    }
    let resolve = |display: &str| -> Vec<Name> {
        by_display
            .get(display)
            .cloned()
            .unwrap_or_else(|| vec![Name::interned(display)])
    };
    let ambiguous = by_display.values().filter(|names| names.len() > 1).count();
    println!("ambiguous display strings: {ambiguous}");

    let mut targets: BTreeSet<Name> = args.targets.iter().flat_map(|t| resolve(t)).collect();
    if let Some(module) = &args.all_theorems_of {
        for display in module_declared(&args.search, module) {
            for name in resolve(&display) {
                if env
                    .get_const(&name)
                    .is_some_and(|c| c.kind == clean_kernel::env::ConstantKind::Theorem)
                {
                    targets.insert(name);
                }
            }
        }
    }
    if args.all_env_constants {
        for c in env.constants() {
            targets.insert(c.name.clone());
        }
    }
    if let Some(cap) = args.max_targets {
        targets = targets.into_iter().take(cap).collect();
    }
    println!("targets    : {}", targets.len());
    if targets.is_empty() {
        println!("nothing to measure");
        return;
    }

    // --- level 1: local assumed-environment check -------------------------
    let t0 = Instant::now();
    // The local check's own API takes display strings.
    let display_targets: BTreeSet<String> = targets.iter().map(ToString::to_string).collect();
    let (pass, fail, errors) = typecheck_constants_full(&env, &display_targets, HEARTBEATS);
    let local_ms = t0.elapsed().as_millis();
    println!("\n-- {} --", RecheckLevel::LocalAssumedEnv.token());
    println!("proves        : {}", RecheckLevel::LocalAssumedEnv.proves());
    println!(
        "does NOT prove: {}",
        RecheckLevel::LocalAssumedEnv.does_not_prove()
    );
    println!("pass/fail  : {pass}/{fail}");
    println!("elapsed_ms : {local_ms}");
    println!("peak_rss   : {}", peak_rss_bytes());
    for (name, error) in errors.iter().take(10) {
        println!("  FAIL {name}: {error}");
    }

    // --- level 3: dependency-closed replay --------------------------------
    let t0 = Instant::now();
    // The binding table is crate-private (always the pinned one here), so the
    // options are adjusted in place rather than built with struct update.
    let mut options = ClosedRecheckOptions::default();
    options.max_heartbeats = HEARTBEATS;
    let run = recheck_closed(&env, &targets, &options);
    let closed_ms = t0.elapsed().as_millis();
    println!("\n-- {} --", RecheckLevel::ClosedReplay.token());
    println!("proves        : {}", RecheckLevel::ClosedReplay.proves());
    println!(
        "does NOT prove: {}",
        RecheckLevel::ClosedReplay.does_not_prove()
    );
    println!("cone consts    : {}", run.report.cone_constants);
    println!("units          : {}", run.report.units);
    println!("consts admitted: {}", run.report.constants_admitted);
    println!("families       : {}", run.report.families_replayed);
    println!("members cmp    : {}", run.report.family_members_compared);
    println!("iota rules cmp : {}", run.report.recursor_rules_compared);
    println!("axioms         : {}", run.report.axioms_admitted.len());
    for a in run.report.axioms_admitted.iter().take(20) {
        println!("  AXIOM {a}");
    }
    println!("refusals       : {}", run.report.refusals.len());
    println!(
        "elapsed_ms     : {closed_ms} (report says {})",
        run.report.elapsed_ms
    );
    println!("peak_rss       : {}", peak_rss_bytes());
    println!(
        "ext. bindings  : {} (pinned: {}), {} keys bound: {:?}",
        run.report.extension_bindings,
        run.report.extension_bindings_pinned,
        run.report.extension_keys_bound.len(),
        run.report.extension_keys_bound
    );
    println!("verdict        : {}", run.report.verdict_sentence());
    println!("passed         : {}", run.report.passed());
    if args.print_extension_bindings {
        println!(
            "\n// extension-key fingerprints this cone declares (root {}):",
            args.root
        );
        for (name, hex) in &run.report.extension_key_fingerprints {
            // A requested target the closure does not declare is still in the
            // cone (as absent) and still fingerprinted; it is not a row.
            if !by_display.contains_key(name) {
                println!("    // {name}: not declared by this closure");
                continue;
            }
            println!("    (\"{name}\", \"{hex}\"),");
        }
    }

    let mut histogram: BTreeMap<&'static str, usize> = BTreeMap::new();
    use clean_olean::recheck_closed::ClosedRecheckRefusal as R;
    for r in &run.report.refusals {
        let key = match r {
            R::AbsentFromEnvironment { .. } => "AbsentFromEnvironment",
            R::DependencyCycle { .. } => "DependencyCycle",
            R::DeclarationRefused { .. } => "DeclarationRefused",
            R::FamilyRefused { .. } => "FamilyRefused",
            R::FamilyIncomplete { .. } => "FamilyIncomplete",
            R::MemberNotRegenerated { .. } => "MemberNotRegenerated",
            R::MemberMismatch { .. } => "MemberMismatch",
            R::RecursorRuleMismatch { .. } => "RecursorRuleMismatch",
            R::DependencyRefused { .. } => "DependencyRefused",
            R::OutsideTrustedFragment { .. } => "OutsideTrustedFragment",
            R::ExtensionBindingMismatch { .. } => "ExtensionBindingMismatch",
            _ => "Other",
        };
        *histogram.entry(key).or_default() += 1;
    }
    println!("\nrefusal histogram:");
    for (kind, count) in &histogram {
        println!("  {kind:24} {count}");
    }
    println!("\nfirst refusals:");
    for r in run.report.refusals.iter().take(25) {
        println!("  {r:?}");
    }
    // Trace every cascade refusal to the primary refusal it descends from, and
    // say whether the cascaded unit is ITSELF outside the trusted fragment
    // (the cascade check runs before the unsafe/partial check, so such a unit
    // is reported as blocked rather than as unsafe).
    let blocked: BTreeMap<&str, &str> = run
        .report
        .refusals
        .iter()
        .filter_map(|r| match r {
            R::DependencyRefused { name, blocked_by } => Some((name.as_str(), blocked_by.as_str())),
            _ => None,
        })
        .collect();
    let mut root_hist: BTreeMap<(String, &'static str), usize> = BTreeMap::new();
    let mut cascade_lines = String::new();
    for name in blocked.keys() {
        let mut root = *name;
        let mut hops = 0usize;
        while let Some(next) = blocked.get(root) {
            root = next;
            hops += 1;
            if hops > blocked.len() {
                break;
            }
        }
        let own = by_display.get(*name).map_or("family-or-unknown", |names| {
            if names.iter().any(|n| env.is_unsafe(n)) {
                "itself-unsafe"
            } else if names.iter().any(|n| env.is_partial(n)) {
                "itself-partial"
            } else {
                "safe"
            }
        });
        *root_hist.entry((root.to_string(), own)).or_default() += 1;
        cascade_lines.push_str(&format!("{name}\troot={root}\thops={hops}\t{own}\n"));
    }
    println!("\ncascade roots (root, the cascaded unit's own fragment status):");
    for ((root, own), count) in &root_hist {
        println!("  {count:4}  {root}  [{own}]");
    }
    if let Some(path) = &args.dump_refusals {
        let cascade_path = path.with_extension("cascade");
        std::fs::write(&cascade_path, &cascade_lines).expect("cascade file must be writable");
        println!("cascade trace written to {}", cascade_path.display());
        let mut text = String::new();
        for r in &run.report.refusals {
            text.push_str(&format!("{}\t{r:?}\n", r.subject()));
        }
        std::fs::write(path, text).expect("--dump-refusals file must be writable");
        println!(
            "\nall {} refusals written to {}",
            run.report.refusals.len(),
            path.display()
        );
    }
}
