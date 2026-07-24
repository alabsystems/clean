// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 2 generator: reflect the foundation core of the LIVE
//! `Specification::new()` kernel environment into the `kernel_core_red_env`
//! generated artifacts (value literal + interning table + skip ledger), and
//! measure the numbers the stage's budget gate needs.
//!
//! Usage:
//!   cargo run --release -p clean-verify --bin red_env_reflect            # emit
//!   cargo run --release -p clean-verify --bin red_env_reflect -- --check # drift check only
//!   cargo run --release -p clean-verify --bin red_env_reflect -- --probe # whnf one-rfl probe
//!
//! Always prints the timed `Specification::new()` build (the build-time budget
//! measurement: run once BEFORE the registration stage lands and once after;
//! the delta is the stage's cost, gated at 20%).
//!
//! Encodings (trust edges) are documented in `clean_verify::red_env_reflect`.

use std::io::Write as _;
use std::time::Instant;

use clean_kernel::{Expr, TypeChecker};
use clean_verify::red_env_reflect::{fidelity_check, reflect_foundation_core};
use clean_verify::Specification;

const GENERATED_DIR: &str = "crates/clean-verify/src/spec/core_spec/generated";

fn main() {
    // Spec construction + reflection recurse deeply; use a big-stack thread
    // (same pattern as the lean_export bin).
    let handle = std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(run)
        .expect("spawn reflect thread");
    match handle.join() {
        Ok(code) => std::process::exit(code),
        Err(_) => std::process::exit(1),
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> i32 {
    let mut check_only = false;
    let mut probe = false;
    for a in std::env::args().skip(1) {
        match a.as_str() {
            "--check" => check_only = true,
            "--probe" => probe = true,
            other => {
                eprintln!("unknown argument: {other}");
                return 2;
            }
        }
    }

    eprintln!("[red_env_reflect] building live Specification::new() (timed) ...");
    let t0 = Instant::now();
    let spec = match Specification::new() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[red_env_reflect] Specification::new() FAILED: {e:?}");
            return 1;
        }
    };
    let build = t0.elapsed();
    eprintln!(
        "[red_env_reflect] Specification::new() built in {:.3}s ({} kernel constants)",
        build.as_secs_f64(),
        spec.env().num_constants()
    );

    let t1 = Instant::now();
    let reflection = reflect_foundation_core(spec.env());
    eprintln!(
        "[red_env_reflect] reflection computed in {:.3}s: {} recursors ({} rules), {} defs, {} interned names, {} skips",
        t1.elapsed().as_secs_f64(),
        reflection.recs.len(),
        reflection.recs.iter().map(|r| r.rules.len()).sum::<usize>(),
        reflection.defs.len(),
        reflection.interning.len(),
        reflection.skips.len()
    );
    if !reflection.interning_injective() {
        eprintln!("[red_env_reflect] FATAL: interning table not injective");
        return 1;
    }

    let script = reflection.def_script();
    let interning = reflection.interning_tsv();
    let ledger = reflection.skip_ledger_md();
    eprintln!(
        "[red_env_reflect] def script: {} bytes ({} defs, max paren depth {}); interning: {} bytes; ledger: {} bytes",
        script.len(),
        script.lines().count(),
        script
            .lines()
            .map(clean_verify::red_env_reflect::max_paren_depth)
            .max()
            .unwrap_or(0),
        interning.len(),
        ledger.len()
    );

    if probe {
        return run_probe(&spec);
    }

    let dir = std::path::Path::new(GENERATED_DIR);
    let script_path = dir.join("kernel_core_red_env.defs.txt");
    let interning_path = dir.join("kernel_core_red_env.interning.tsv");
    let ledger_path = dir.join("kernel_core_red_env.skips.md");

    if check_only {
        let committed_script = std::fs::read_to_string(&script_path).unwrap_or_default();
        let committed_interning = std::fs::read_to_string(&interning_path).unwrap_or_default();
        let committed_ledger = std::fs::read_to_string(&ledger_path).unwrap_or_default();
        return match fidelity_check(
            spec.env(),
            &committed_script,
            &committed_interning,
            &committed_ledger,
        ) {
            Ok(_) => {
                eprintln!("[red_env_reflect] fidelity check PASSED (no drift)");
                0
            }
            Err(e) => {
                eprintln!("[red_env_reflect] fidelity check FAILED: {e}");
                1
            }
        };
    }

    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("[red_env_reflect] cannot create {GENERATED_DIR}: {e}");
        return 1;
    }
    for (path, content) in [
        (&script_path, script),
        (&interning_path, interning),
        (&ledger_path, ledger),
    ] {
        match std::fs::File::create(path).and_then(|mut f| f.write_all(content.as_bytes())) {
            Ok(()) => eprintln!("[red_env_reflect] wrote {}", path.display()),
            Err(e) => {
                eprintln!("[red_env_reflect] cannot write {}: {e}", path.display());
                return 1;
            }
        }
    }
    0
}

/// The one-rfl-at-scale PROBE (Stage-4 feasibility preview): whnf-evaluate
/// each Stage-1 closure checker over the registered `kernel_core_red_env`
/// and time the fold. Requires the registration stage to be in the spec.
fn run_probe(spec: &Specification) -> i32 {
    if spec
        .env()
        .get_const(&clean_kernel::Name::from_string("kernel_core_red_env"))
        .is_none()
    {
        eprintln!(
            "[red_env_reflect] --probe: kernel_core_red_env not registered in the spec \
             (run after the Stage-2 registration stage lands)"
        );
        return 1;
    }
    let tc = TypeChecker::new(spec.env());
    let mut code = 0;
    for (checker, proj) in [
        ("rec_env_closed_b", "red_rec"),
        ("rec_env_lift_closed_b", "red_rec"),
        ("def_env_closed_b", "red_def"),
        ("def_env_lift_closed_b", "red_def"),
    ] {
        let e = Expr::app(
            Expr::const_str(checker),
            Expr::app(
                Expr::const_str(proj),
                Expr::const_str("kernel_core_red_env"),
            ),
        );
        let t = Instant::now();
        let w = tc.whnf(&e);
        let dt = t.elapsed();
        let head = format!("{w}");
        eprintln!(
            "[red_env_reflect] probe {checker} ({proj} kernel_core_red_env): whnf = {} in {:.3}s",
            head.chars().take(80).collect::<String>(),
            dt.as_secs_f64()
        );
        if !(head.starts_with("Bool.true") || head.starts_with("Bool.false")) {
            eprintln!("[red_env_reflect] probe {checker}: fold STUCK (non-Bool head)");
            code = 1;
        }
    }

    // Aggregate per-element cost (the TRUE-case fold cost the Bool.and
    // short-circuit hides): force the full per-element checker test
    // `nat_eqb (bvar_ceiling <term>) 0` for every reflected rule rhs and
    // def value, and total the whnf time. This is the measured one-rfl
    // budget for a Stage-4 depth-aware checker at real-env scale.
    let reflection = reflect_foundation_core(spec.env());
    let mut elements: Vec<(String, &clean_verify::red_env_reflect::SpecExpr)> = Vec::new();
    for rec in &reflection.recs {
        for rule in &rec.rules {
            elements.push((format!("{}/{}", rec.name, rule.ctor), &rule.rhs));
        }
    }
    for def in &reflection.defs {
        elements.push((def.name.clone(), &def.value));
    }
    let mut total = std::time::Duration::ZERO;
    let mut worst = (String::new(), std::time::Duration::ZERO);
    let mut trues = 0usize;
    for (label, term) in &elements {
        let e = Expr::apps(
            Expr::const_str("nat_eqb"),
            [
                Expr::app(Expr::const_str("bvar_ceiling"), reflection.kexpr_term(term)),
                Expr::const_str("kcre_nat_0"),
            ],
        );
        let t = Instant::now();
        let w = tc.whnf(&e);
        let dt = t.elapsed();
        total += dt;
        if dt > worst.1 {
            worst = (label.clone(), dt);
        }
        let head = format!("{w}");
        if head.starts_with("Bool.true") {
            trues += 1;
        } else if !head.starts_with("Bool.false") {
            eprintln!("[red_env_reflect] element probe {label}: STUCK (non-Bool head {head})");
            code = 1;
        }
    }
    eprintln!(
        "[red_env_reflect] element probes: {} elements, {} ceiling-0 (bvar-free), total {:.3}s, worst {} at {:.3}s",
        elements.len(),
        trues,
        total.as_secs_f64(),
        worst.0,
        worst.1.as_secs_f64()
    );
    code
}
