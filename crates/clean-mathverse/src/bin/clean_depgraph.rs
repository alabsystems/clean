// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean-depgraph` — hard-theorem dependency-graph analyzer (#3595).
//!
//! Lets agents pick the highest-leverage next-unblockable lemma instead of
//! guessing. Seeds a kernel `Environment` with the same math-overlay
//! declarations that the clean-Native shard builder uses, walks the
//! transitive `Expr::Const` closure of a headline claim (T60 / C004 /
//! C006), classifies every node (axiom / theorem / definition / trust
//! marker), and ranks promotion candidates by the number of closure nodes
//! that transitively depend on them.
//!
//! ```text
//! clean-depgraph --headline T60                 # JSON DAG
//! clean-depgraph --unblock T60 --limit 5        # top-5 ranked promotion targets
//! clean-depgraph --impact NNVerify.Block.crown  # per-headline leverage for a lemma
//! clean-depgraph --graphviz T60 > t60.dot       # DOT visualization
//! ```
//!
//! See `reports/depgraph/*.dot` / `*.txt` for committed artifacts.

use std::process::ExitCode;

use clean_kernel::{Environment, Name};
use clean_mathverse::depgraph::{
    build_closure, emit_dot, emit_headline_json, emit_impact_text, emit_unblock_text,
    headline_name, rank_unblock_candidates, seed_environment, KNOWN_HEADLINES,
};

#[derive(Debug)]
enum Mode {
    Headline { alias: String },
    Unblock { alias: String, limit: Option<usize> },
    Impact { lemma: String },
    Graphviz { alias: String },
    ListHeadlines,
    Help,
}

fn parse_args(raw: &[String]) -> Result<Mode, String> {
    let mut iter = raw.iter().peekable();
    let mut mode: Option<Mode> = None;
    let mut limit: Option<usize> = None;
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--headline" => {
                let v = iter.next().ok_or("--headline requires an argument")?;
                mode = Some(Mode::Headline { alias: v.clone() });
            }
            "--unblock" => {
                let v = iter.next().ok_or("--unblock requires an argument")?;
                mode = Some(Mode::Unblock {
                    alias: v.clone(),
                    limit,
                });
            }
            "--impact" => {
                let v = iter.next().ok_or("--impact requires an argument")?;
                mode = Some(Mode::Impact { lemma: v.clone() });
            }
            "--graphviz" | "--dot" => {
                let v = iter.next().ok_or("--graphviz requires an argument")?;
                mode = Some(Mode::Graphviz { alias: v.clone() });
            }
            "--limit" => {
                let v = iter.next().ok_or("--limit requires an argument")?;
                let parsed: usize = v
                    .parse()
                    .map_err(|e| format!("--limit must be a non-negative integer: {e}"))?;
                limit = Some(parsed);
                // If --unblock was already parsed, retrofit the limit.
                if let Some(Mode::Unblock {
                    alias: _,
                    limit: ref mut l,
                }) = mode
                {
                    *l = Some(parsed);
                }
            }
            "--list-headlines" => mode = Some(Mode::ListHeadlines),
            "-h" | "--help" => mode = Some(Mode::Help),
            other => return Err(format!("unknown argument: {other}")),
        }
    }
    // Re-apply a trailing --limit to a previously-parsed --unblock mode.
    if let (Some(Mode::Unblock { alias, .. }), Some(l)) = (&mode, limit) {
        mode = Some(Mode::Unblock {
            alias: alias.clone(),
            limit: Some(l),
        });
    }
    mode.ok_or_else(|| "no mode specified; try --help".to_string())
}

fn print_help() {
    println!(
        "clean-depgraph — hard-theorem dependency graph analyzer (#3595)\n\n\
         USAGE:\n  \
             clean-depgraph --headline <ALIAS|NAME>\n  \
             clean-depgraph --unblock <ALIAS|NAME> [--limit N]\n  \
             clean-depgraph --impact <LEMMA_NAME>\n  \
             clean-depgraph --graphviz <ALIAS|NAME>\n  \
             clean-depgraph --list-headlines\n\n\
         ALIASES:"
    );
    for (short, full) in KNOWN_HEADLINES {
        println!("  {short:<6} -> {full}");
    }
    println!(
        "\nFull kernel names are accepted directly. Ranking selects domain-specific\n\
         axioms and trust markers; promoting a high-impact entry unblocks the\n\
         largest closure sub-tree.\n\n\
         See `reports/depgraph/*.dot` and `.txt` for committed artifacts."
    );
}

fn cmd_headline(env: &Environment, alias: &str) -> Result<(), String> {
    let full = headline_name(alias);
    let name = Name::from_string(&full);
    let graph = build_closure(env, &name)
        .ok_or_else(|| format!("headline `{full}` is not registered in the seeded environment"))?;
    println!("{}", emit_headline_json(&graph));
    Ok(())
}

fn cmd_unblock(env: &Environment, alias: &str, limit: Option<usize>) -> Result<(), String> {
    let full = headline_name(alias);
    let name = Name::from_string(&full);
    let graph = build_closure(env, &name)
        .ok_or_else(|| format!("headline `{full}` is not registered in the seeded environment"))?;
    let ranked = rank_unblock_candidates(&graph, limit);
    println!("{}", emit_unblock_text(&graph.root, &ranked));
    Ok(())
}

fn cmd_graphviz(env: &Environment, alias: &str) -> Result<(), String> {
    let full = headline_name(alias);
    let name = Name::from_string(&full);
    let graph = build_closure(env, &name)
        .ok_or_else(|| format!("headline `{full}` is not registered in the seeded environment"))?;
    println!("{}", emit_dot(&graph));
    Ok(())
}

fn cmd_impact(env: &Environment, lemma: &str) -> Result<(), String> {
    let mut results: Vec<(String, usize, usize)> = Vec::new();
    for (short, full) in KNOWN_HEADLINES {
        let root = Name::from_string(full);
        let Some(graph) = build_closure(env, &root) else {
            continue;
        };
        if let Some(node) = graph.nodes.get(lemma) {
            let direct = graph
                .nodes
                .values()
                .filter(|m| m.direct_deps.iter().any(|d| d == lemma))
                .count();
            results.push((format!("{short} ({full})"), node.impact, direct));
        }
    }
    println!("{}", emit_impact_text(lemma, &results));
    Ok(())
}

fn cmd_list_headlines() {
    println!("Known headline aliases (short -> full kernel name):\n");
    for (short, full) in KNOWN_HEADLINES {
        println!("  {short:<6} -> {full}");
    }
}

fn run() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = match parse_args(&args) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: {e}");
            eprintln!();
            print_help();
            return ExitCode::from(2);
        }
    };

    // Seed once per invocation. Cheap — each init_nn_verify_* is a bounded
    // registration loop. ~tens of ms.
    let mut env = Environment::new();
    seed_environment(&mut env);

    let result = match mode {
        Mode::Headline { alias } => cmd_headline(&env, &alias),
        Mode::Unblock { alias, limit } => cmd_unblock(&env, &alias, limit),
        Mode::Impact { lemma } => cmd_impact(&env, &lemma),
        Mode::Graphviz { alias } => cmd_graphviz(&env, &alias),
        Mode::ListHeadlines => {
            cmd_list_headlines();
            Ok(())
        }
        Mode::Help => {
            print_help();
            Ok(())
        }
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    run()
}
