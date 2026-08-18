// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof infrastructure CLI commands: axiom audit and proof search.
//!
//! These subcommands load `.mathverse` shards into a kernel `Environment` and
//! run axiom dependency analysis (`audit`) or proof search (`proof-search`).

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

pub(crate) fn cmd_audit(args: &[String]) {
    use clean_mathverse::shard_verify::discover_mathverse_files;

    let shard_dir = Path::new(&args[0]);
    let mut json_output: Option<PathBuf> = None;
    let mut single_name: Option<String> = None;

    for arg in &args[1..] {
        if let Some(val) = arg.strip_prefix("--json=") {
            json_output = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--name=") {
            single_name = Some(val.to_string());
        } else {
            eprintln!("Unknown option: {arg}");
            std::process::exit(1);
        }
    }

    println!("=== Mathverse Shard Axiom Audit ===");
    println!("  Directory: {}\n", shard_dir.display());

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files", mathverse_files.len());

    // Build environment incrementally from all shards.
    let start = Instant::now();
    let env = load_env_from_shards(&mathverse_files);
    println!(
        "  Environment loaded: {} constants ({:.2}s)\n",
        env.num_constants(),
        start.elapsed().as_secs_f64()
    );

    if let Some(ref name) = single_name {
        let n = clean_kernel::Name::from_string(name);
        match env.proof_quality(&n) {
            Some(quality) => print_single_audit(name, &quality, &env),
            None => {
                eprintln!("  Declaration not found: {name}");
                std::process::exit(1);
            }
        }
    } else {
        let report_start = Instant::now();
        let report = env.soundness_report();
        print_soundness_report(&report, report_start.elapsed());
        if let Some(ref path) = json_output {
            write_audit_json(&report, path);
        }
    }
}

fn print_single_audit(
    name: &str,
    quality: &clean_kernel::ProofQuality,
    env: &clean_kernel::Environment,
) {
    use clean_kernel::ProofQuality;

    println!("  Declaration: {name}");
    match quality {
        ProofQuality::Constructive => {
            println!("  Quality:     Constructive (zero domain-specific axioms)");
        }
        ProofQuality::AxiomDependent {
            axiom_count,
            axioms,
        } => {
            println!("  Quality:     AxiomDependent ({axiom_count} domain axioms)");
            println!("  Axioms:");
            for ax in axioms {
                println!("    - {ax}");
            }
        }
        ProofQuality::NotATheorem => {
            println!("  Quality:     NotATheorem (axiom, definition, or opaque)");
        }
        ProofQuality::Unchecked => {
            println!("  Quality:     Unchecked (not kernel-verified)");
        }
        _ => {
            println!("  Quality:     Unknown");
        }
    }

    let n = clean_kernel::Name::from_string(name);
    if let Some(deps) = env.axiom_deps(&n) {
        if deps.is_empty() {
            println!("  Axiom deps:  none (clean)");
        } else {
            println!("  Axiom deps:  {}", deps.len());
            let mut sorted: Vec<_> = deps.iter().map(|d| d.to_string()).collect();
            sorted.sort();
            for d in &sorted {
                println!("    - {d}");
            }
        }
    }
}

fn print_soundness_report(report: &clean_kernel::SoundnessReport, elapsed: std::time::Duration) {
    println!("=== Soundness Report ===");
    println!(
        "  Total declarations:          {}",
        report.total_declarations
    );
    println!("  Theorems:                    {}", report.theorems);
    println!("  Axioms:                      {}", report.axioms);
    println!("  Definitions:                 {}", report.definitions);
    println!("  Opaques:                     {}", report.opaques);
    println!();
    println!(
        "  Constructive theorems:       {}",
        report.constructive_theorems
    );
    println!(
        "  Axiom-dependent theorems:    {}",
        report.axiom_dependent_theorems
    );
    println!(
        "  Unchecked declarations:      {}",
        report.unchecked_declarations
    );
    println!(
        "  Domain-specific axioms:      {}",
        report.total_domain_axioms
    );
    println!(
        "  Audit elapsed:               {:.2}s",
        elapsed.as_secs_f64()
    );

    if report.theorems > 0 {
        let pct = report.constructive_theorems as f64 / report.theorems as f64 * 100.0;
        println!("  Constructive rate:           {pct:.1}%");
    }

    if !report.domain_axioms.is_empty() {
        println!("\n  Domain axioms (first 50):");
        for ax in report.domain_axioms.iter().take(50) {
            println!("    - {ax}");
        }
        if report.domain_axioms.len() > 50 {
            println!("    ... and {} more", report.domain_axioms.len() - 50);
        }
    }
}

fn write_audit_json(report: &clean_kernel::SoundnessReport, path: &Path) {
    let json = serde_json::json!({
        "total_declarations": report.total_declarations,
        "theorems": report.theorems,
        "axioms": report.axioms,
        "definitions": report.definitions,
        "opaques": report.opaques,
        "constructive_theorems": report.constructive_theorems,
        "axiom_dependent_theorems": report.axiom_dependent_theorems,
        "unchecked_declarations": report.unchecked_declarations,
        "total_domain_axioms": report.total_domain_axioms,
        "domain_axioms": report.domain_axioms.iter().map(|a| a.to_string()).collect::<Vec<_>>(),
    });

    match serde_json::to_string_pretty(&json) {
        Ok(s) => match fs::write(path, s) {
            Ok(()) => println!("\n  Audit JSON written to: {}", path.display()),
            Err(e) => eprintln!("\n  Warning: failed to write JSON: {e}"),
        },
        Err(e) => eprintln!("\n  Warning: failed to serialize JSON: {e}"),
    }
}

pub(crate) fn cmd_proof_search(args: &[String]) {
    use clean_mathverse::shard_verify::discover_mathverse_files;

    let shard_dir = Path::new(&args[0]);
    let mut json_output: Option<PathBuf> = None;
    let mut goal_name: Option<String> = None;
    let mut budget: usize = 10_000;

    for arg in &args[1..] {
        if let Some(val) = arg.strip_prefix("--json=") {
            json_output = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--goal=") {
            goal_name = Some(val.to_string());
        } else if let Some(val) = arg.strip_prefix("--budget=") {
            budget = val.parse().unwrap_or_else(|_| {
                eprintln!("Invalid --budget value: {val}");
                std::process::exit(1);
            });
        } else {
            eprintln!("Unknown option: {arg}");
            std::process::exit(1);
        }
    }

    println!("=== Mathverse Shard Proof Search ===");
    println!("  Directory: {}", shard_dir.display());
    println!("  Budget:    {budget}\n");

    let mathverse_files = discover_mathverse_files(shard_dir);
    if mathverse_files.is_empty() {
        eprintln!("  No .mathverse files found in {}", shard_dir.display());
        std::process::exit(1);
    }
    println!("  Found {} shard files", mathverse_files.len());

    let start = Instant::now();
    let env = load_env_from_shards(&mathverse_files);
    println!(
        "  Environment loaded: {} constants ({:.2}s)\n",
        env.num_constants(),
        start.elapsed().as_secs_f64()
    );

    if let Some(ref name) = goal_name {
        search_single_goal(&env, name, budget);
    } else {
        search_all_theorems(&env, budget, &json_output);
    }
}

fn search_single_goal(env: &clean_kernel::Environment, name: &str, budget: usize) {
    use clean_kernel::env::proof_search::{search_proof, ProofSearchResult};

    let n = clean_kernel::Name::from_string(name);
    let Some(info) = env.get_const(&n) else {
        eprintln!("  Declaration not found: {name}");
        std::process::exit(1);
    };

    println!("  Searching for proof of: {name}");
    let search_start = Instant::now();
    let result = search_proof(env, &info.type_, budget);
    let elapsed = search_start.elapsed();

    match result {
        ProofSearchResult::Found { strategy, .. } => {
            println!("  FOUND via strategy: {strategy}");
            println!("  Time: {:.4}s", elapsed.as_secs_f64());
        }
        ProofSearchResult::Exhausted { candidates_tried } => {
            println!("  EXHAUSTED after {candidates_tried} candidates");
            println!("  Time: {:.4}s", elapsed.as_secs_f64());
        }
        ProofSearchResult::BudgetExceeded {
            candidates_tried,
            budget,
        } => {
            println!("  BUDGET EXCEEDED: tried {candidates_tried}/{budget}");
            println!("  Time: {:.4}s", elapsed.as_secs_f64());
        }
    }
}

fn search_all_theorems(
    env: &clean_kernel::Environment,
    budget: usize,
    json_output: &Option<PathBuf>,
) {
    use clean_kernel::env::proof_search::{search_proof, ProofSearchResult};
    use clean_kernel::ConstantKind;

    let theorems: Vec<_> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Theorem)
        .collect();
    let total = theorems.len();
    println!("  Searching {total} theorems (budget {budget} per goal)...\n");

    let mut found = 0usize;
    let mut exhausted = 0usize;
    let mut budget_exceeded = 0usize;
    let mut results_json = Vec::new();
    let start = Instant::now();

    for (i, info) in theorems.iter().enumerate() {
        let name_str = info.name.to_string();
        let result = search_proof(env, &info.type_, budget);

        match &result {
            ProofSearchResult::Found { strategy, .. } => {
                found += 1;
                println!("  FOUND  {name_str} (strategy: {strategy})");
                results_json.push(serde_json::json!({
                    "name": name_str, "result": "found", "strategy": strategy,
                }));
            }
            ProofSearchResult::Exhausted { candidates_tried } => {
                exhausted += 1;
                results_json.push(serde_json::json!({
                    "name": name_str, "result": "exhausted",
                    "candidates_tried": candidates_tried,
                }));
            }
            ProofSearchResult::BudgetExceeded {
                candidates_tried,
                budget,
            } => {
                budget_exceeded += 1;
                results_json.push(serde_json::json!({
                    "name": name_str, "result": "budget_exceeded",
                    "candidates_tried": candidates_tried, "budget": budget,
                }));
            }
        }

        if (i + 1) % 100 == 0 {
            println!(
                "  ... {}/{total} ({found} found, {:.1}s)",
                i + 1,
                start.elapsed().as_secs_f64()
            );
        }
    }

    let elapsed = start.elapsed();
    println!("\n=== Proof Search Summary ===");
    println!("  Theorems searched:   {total}");
    println!("  Proofs found:        {found}");
    println!("  Exhausted:           {exhausted}");
    println!("  Budget exceeded:     {budget_exceeded}");
    println!("  Elapsed:             {:.2}s", elapsed.as_secs_f64());
    if total > 0 {
        println!(
            "  Success rate:        {:.1}%",
            found as f64 / total as f64 * 100.0
        );
    }

    if let Some(ref path) = json_output {
        let json = serde_json::json!({
            "total_theorems": total,
            "proofs_found": found,
            "exhausted": exhausted,
            "budget_exceeded": budget_exceeded,
            "elapsed_secs": elapsed.as_secs_f64(),
            "results": results_json,
        });
        match serde_json::to_string_pretty(&json) {
            Ok(s) => match fs::write(path, s) {
                Ok(()) => println!("\n  Results written to: {}", path.display()),
                Err(e) => eprintln!("\n  Warning: failed to write JSON: {e}"),
            },
            Err(e) => eprintln!("\n  Warning: failed to serialize JSON: {e}"),
        }
    }
}

/// Load all mathverse shards into a kernel `Environment`.
///
/// Reads each shard, reconstructs declarations via topological ordering,
/// and adds them to a shared environment through the trusted import-boundary
/// bulk hook (`TrustedEnvExt::extend_constants_structural`); every constant
/// is stamped `StructuralOnly`, never `KernelVerified`.
fn load_env_from_shards(mathverse_files: &[PathBuf]) -> clean_kernel::Environment {
    use clean_mathverse::shard::ShardReader;

    let mut env = clean_kernel::Environment::new();

    for path in mathverse_files {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let reader = match ShardReader::from_file(path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("  SKIP {name}: {e}");
                continue;
            }
        };
        let before = env.num_constants();
        add_shard_to_env(&mut env, &reader);
        let added = env.num_constants() - before;
        println!(
            "  {name}: {} constants, {added} added",
            reader.constants.len()
        );
    }

    env
}

/// Add all reconstructable constants from a shard to the environment.
fn add_shard_to_env(
    env: &mut clean_kernel::Environment,
    reader: &clean_mathverse::shard::ShardReader,
) {
    use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility, TrustedEnvExt};
    use clean_kernel::Name;
    use clean_mathverse::shard_reconstruct::reconstruct_from_shard;
    use clean_mathverse::types::NO_VALUE;
    use clean_mathverse::verify::incremental::build_dependency_graph;

    let dep_graph = build_dependency_graph(reader);

    let mut order = Vec::new();
    let mut visited = std::collections::HashSet::new();
    let mut temp_visited = std::collections::HashSet::new();

    fn dfs(
        node: &str,
        deps: &std::collections::HashMap<String, std::collections::HashSet<String>>,
        visited: &mut std::collections::HashSet<String>,
        temp_visited: &mut std::collections::HashSet<String>,
        order: &mut Vec<String>,
    ) {
        if visited.contains(node) || temp_visited.contains(node) {
            return;
        }
        temp_visited.insert(node.to_string());
        if let Some(node_deps) = deps.get(node) {
            for dep in node_deps {
                dfs(dep, deps, visited, temp_visited, order);
            }
        }
        temp_visited.remove(node);
        visited.insert(node.to_string());
        order.push(node.to_string());
    }

    for name in dep_graph.keys() {
        dfs(
            name,
            &dep_graph,
            &mut visited,
            &mut temp_visited,
            &mut order,
        );
    }

    let name_to_idx: std::collections::HashMap<&str, usize> = reader
        .constants
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            reader
                .strings
                .get(c.name_idx as usize)
                .map(|s| (s.as_str(), i))
        })
        .collect();

    let mut batch: Vec<ConstantInfo> = Vec::new();
    for name in &order {
        let Some(&idx) = name_to_idx.get(name.as_str()) else {
            continue;
        };
        let constant = &reader.constants[idx];

        let n = Name::from_string(name);
        // extend_constants_structural does not duplicate-check (a same-name
        // insert would overwrite); pre-filter names already registered so the
        // first shard providing a constant wins, matching the DuplicateName
        // skip of the retired per-decl add_decl_structural path. Names within
        // one batch are unique (topological order visits each name once).
        if env.get_const(&n).is_some() {
            continue;
        }

        let Ok(type_expr) = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        ) else {
            continue;
        };

        let value = if constant.value_idx != NO_VALUE {
            reconstruct_from_shard(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                constant.value_idx,
            )
            .ok()
        } else {
            None
        };

        let decl_kind = clean_mathverse::types::DeclKind::try_from(constant.decl_kind)
            .unwrap_or(clean_mathverse::types::DeclKind::Theorem);

        let (kind, reducibility, value) = match decl_kind {
            clean_mathverse::types::DeclKind::Theorem => (
                ConstantKind::Theorem,
                Reducibility::Opaque,
                Some(value.unwrap_or_else(clean_kernel::Expr::prop)),
            ),
            clean_mathverse::types::DeclKind::Axiom => {
                (ConstantKind::Axiom, Reducibility::Regular(0), None)
            }
            clean_mathverse::types::DeclKind::Opaque => (
                ConstantKind::Opaque,
                Reducibility::Opaque,
                Some(value.unwrap_or_else(clean_kernel::Expr::prop)),
            ),
            // Height 0 instead of the kernel-computed unfold height: the
            // height only orders delta-unfolding heuristics, and this audit
            // env already erases level params / substitutes placeholder
            // values, so definition heights carry no signal here.
            clean_mathverse::types::DeclKind::Definition => (
                ConstantKind::Definition,
                Reducibility::Regular(0),
                Some(value.unwrap_or_else(clean_kernel::Expr::prop)),
            ),
            // Inductive-family and quotient types: add as axioms since the
            // environment doesn't have the full inductive machinery.
            _ => (ConstantKind::Axiom, Reducibility::Regular(0), None),
        };

        batch.push(ConstantInfo::new_with_reducibility(
            n,
            Vec::new(),
            type_expr,
            value,
            reducibility,
            kind,
        ));
    }

    // SOUNDNESS: import-boundary structural registration, ratcheted in
    // data/unchecked_decl_ratchet.json (extend_constants block). This builds a
    // READ-ONLY audit/proof-search environment from pre-verified shard data:
    // it mints no KernelVerified verdict, is never re-exported, and never
    // enters the kernel TCB. extend_constants_structural runs the same O(1)
    // structural checks (no metavars/fvars, level-param scope) the retired
    // per-decl add_decl_structural path ran and stamps every constant
    // StructuralOnly; per-constant rejections are dropped best-effort exactly
    // like the old ignored per-decl errors. A wrong shard byte can at worst
    // produce a wrong audit finding, never a false trust verdict.
    let _ = env.extend_constants_structural(batch.into_iter());
}
