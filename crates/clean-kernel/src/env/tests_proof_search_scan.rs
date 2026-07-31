// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof search scan across ALL gamma-crown conjectures (C001-C030).
//!
//! Initializes each conjecture's environment, collects all domain-specific
//! `Declaration::Axiom` entries (excluding Lean 4 foundational axioms), and
//! runs proof search on each axiom's type to find axioms that can be
//! automatically proved.
//!
//! Three strategies are available:
//! - **refl**: `Eq.refl` for definitionally-equal sides (WHNF reduction)
//! - **trivial_prop**: `True.intro` for Prop goals
//! - **lookup**: Scan environment for type-matching declarations (excluding self
//!   and transitive axiom dependencies -- see full scan test)
//!
//! ## Results (2026-04-17)
//!
//! Scanned 192 domain axioms across 14/15 conjectures (C006 init fails due to
//! missing `Rat.le_refl`). **Zero axioms are auto-provable** via refl or
//! trivial_prop. These are genuine mathematical axioms, not definitional
//! equalities -- they require real proofs (induction, algebraic manipulation,
//! triangle inequality, etc.).
//!
//! The full lookup scan (with proper transitive-dependency filtering) also
//! found zero genuine matches before encountering stack overflow on deeply
//! nested types.

use crate::env::axiom_audit::is_foundational_axiom;
use crate::env::proof_search::{mk_eq_refl, parse_eq_goal, try_verify_proof};
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Foundational axioms that are not domain-specific.
///
/// Delegates to `axiom_audit::is_foundational_axiom` as the single source of
/// truth for the foundational whitelist (#3560/#3561). Prior to consolidation
/// this module carried its own hard-coded `matches!(...)` copy which drifted
/// from the canonical `axiom_audit::FOUNDATIONAL_AXIOMS` list — it still
/// listed `sorryAx` (moved to `TRUST_MARKERS` in #3554) and `Eq.symm` /
/// `Eq.trans` / `Eq.subst` (demoted to `Declaration::Theorem` in #3559),
/// and was missing the Rat ring / field axiom batches (#3551/#3555), Rat
/// min/max, `Fin.castSucc` / `Fin.last`, and `Nat.le_refl`. Using the
/// canonical predicate keeps this scan automatically in sync with any
/// future whitelist edit.
fn is_foundational(name: &str) -> bool {
    is_foundational_axiom(&Name::from_string(name))
}

/// Initialize a conjecture environment, returning None if init fails.
fn init_conjecture(id: &str) -> Option<Environment> {
    let mut env = Environment::new();
    let result = match id {
        "C001" => env.init_nn_verify_c001(),
        "C002" => env.init_nn_verification_c002(),
        "C003" => env.init_nn_verify_eclipse_convergence(),
        "C004" => env.init_nn_verify_crown_layernorm(),
        "C005" => env.init_nn_verify_mccormick_attention(),
        "C006" => env.init_nn_verify_blockwise_crown(),
        "C007" => env.init_nn_verify_streaming_certs(),
        "C008" => env.init_nn_verify_ibp_tightness(),
        "C009" => env.init_nn_verification_c009(),
        "C010" => env.init_nn_verify_zonotope_crown(),
        "C011" => env.init_nn_verify_softmax_c011(),
        "C012" => env.init_nn_verify_relu_stability(),
        "C028" => env.init_nn_verify_nullstellensatz(),
        "C029" => env.init_nn_verify_pac_proof(),
        "C030" => env.init_nn_verify_orbit_crown(),
        _ => return None,
    };
    match result {
        Ok(()) => Some(env),
        Err(e) => {
            eprintln!("  INIT FAILED for {id}: {e}");
            None
        }
    }
}

/// Collect all domain-specific axioms from an environment, excluding
/// foundational axioms. Returns only NNVerify/NNVerification namespace axioms.
fn collect_domain_axioms(env: &Environment) -> Vec<(Name, Expr)> {
    let mut axioms = Vec::new();
    for info in env.constants() {
        if info.kind != ConstantKind::Axiom {
            continue;
        }
        let name_str = info.name.to_string();
        if is_foundational(&name_str) {
            continue;
        }
        if name_str.starts_with("NNVerify.") || name_str.starts_with("NNVerification.") {
            axioms.push((info.name.clone(), info.type_.clone()));
        }
    }
    axioms.sort_by_key(|a| a.0.to_string());
    axioms
}

/// Targeted proof attempt: try refl for Eq goals, True.intro for Prop goals.
/// These are the cheap strategies that would reveal "free wins" from
/// definition-axiom conversions making both sides definitionally equal.
fn try_targeted_proof(env: &Environment, goal_type: &Expr) -> Option<(&'static str, Expr)> {
    let tc = TypeChecker::with_mode(env, env.mode());

    // Strategy 1: refl for Eq goals where both sides reduce to the same WHNF
    if let Some((ty, levels, lhs, rhs)) = parse_eq_goal(goal_type) {
        if tc.is_def_eq(&lhs, &rhs) {
            let proof = mk_eq_refl(&levels, &ty, &lhs);
            if try_verify_proof(env, goal_type, &proof) {
                return Some(("refl", proof));
            }
        }
    }

    // Strategy 2: True.intro for trivially-true Prop goals
    let proof = Expr::const_str("True.intro");
    if try_verify_proof(env, goal_type, &proof) {
        return Some(("trivial_prop", proof));
    }

    None
}

/// The main scan test: targeted strategies (refl + trivial_prop) on all 15
/// gamma-crown conjectures, individually initialized.
///
/// This is the primary diagnostic test. It initializes each conjecture in its
/// own Environment (capturing the full dependency chain) and tries refl and
/// trivial_prop on every domain axiom.
#[test]
fn test_proof_search_scan_all_conjectures() {
    let conjectures = [
        "C001", "C002", "C003", "C004", "C005", "C006", "C007", "C008", "C009", "C010", "C011",
        "C012", "C028", "C029", "C030",
    ];

    let mut total_axioms = 0usize;
    let mut total_found = 0usize;
    let mut all_found: Vec<(String, String, String)> = Vec::new();

    eprintln!("\n=== PROOF SEARCH SCAN: gamma-crown conjectures (refl + trivial_prop) ===\n");

    for &id in &conjectures {
        let env = match init_conjecture(id) {
            Some(e) => e,
            None => {
                eprintln!("{id}: INIT FAILED\n");
                continue;
            }
        };

        let axioms = collect_domain_axioms(&env);
        let total = axioms.len();
        let mut found = Vec::new();
        let mut not_found_names = Vec::new();

        for (name, type_) in &axioms {
            match try_targeted_proof(&env, type_) {
                Some((strategy, _)) => found.push((name.to_string(), strategy.to_string())),
                None => not_found_names.push(name.to_string()),
            }
        }

        total_axioms += total;
        total_found += found.len();

        eprintln!("{id}: {}/{total} auto-provable", found.len());
        for (name, strategy) in &found {
            eprintln!("  FOUND via {strategy}: {name}");
            all_found.push((id.to_string(), name.clone(), strategy.clone()));
        }
        for name in &not_found_names {
            eprintln!("  NOT FOUND: {name}");
        }
        eprintln!();
    }

    eprintln!("=== SUMMARY ===");
    eprintln!("Total domain axioms scanned: {total_axioms}");
    eprintln!("Auto-provable (refl/trivial): {total_found}");
    eprintln!(
        "Remaining:                    {}",
        total_axioms - total_found
    );

    if !all_found.is_empty() {
        eprintln!("\n=== FREE WINS ===");
        for (conj, name, strategy) in &all_found {
            eprintln!("  {conj} -- {name} (via {strategy})");
        }
    }
}

/// Initialize the full combined environment with all 15 conjectures.
fn init_full_environment() -> Environment {
    let mut env = Environment::new();
    let inits = [
        ("C001", env.init_nn_verify_c001().is_ok()),
        ("C002", env.init_nn_verification_c002().is_ok()),
        ("C003", env.init_nn_verify_eclipse_convergence().is_ok()),
        ("C004", env.init_nn_verify_crown_layernorm().is_ok()),
        ("C005", env.init_nn_verify_mccormick_attention().is_ok()),
        ("C006", env.init_nn_verify_blockwise_crown().is_ok()),
        ("C007", env.init_nn_verify_streaming_certs().is_ok()),
        ("C008", env.init_nn_verify_ibp_tightness().is_ok()),
        ("C009", env.init_nn_verification_c009().is_ok()),
        ("C010", env.init_nn_verify_zonotope_crown().is_ok()),
        ("C011", env.init_nn_verify_softmax_c011().is_ok()),
        ("C012", env.init_nn_verify_relu_stability().is_ok()),
        ("C028", env.init_nn_verify_nullstellensatz().is_ok()),
        ("C029", env.init_nn_verify_pac_proof().is_ok()),
        ("C030", env.init_nn_verify_orbit_crown().is_ok()),
    ];
    eprintln!("\n=== FULL ENVIRONMENT INIT STATUS ===");
    for (id, ok) in &inits {
        eprintln!("  {id}: {}", if *ok { "OK" } else { "FAILED" });
    }
    env
}

/// Results from the full scan with lookup strategy.
struct FullScanResults {
    found_refl: Vec<String>,
    found_trivial: Vec<String>,
    found_lookup: Vec<(String, String, ConstantKind)>,
    not_found: Vec<String>,
}

/// Try the genuine lookup strategy on a single axiom: scan environment for
/// type-matching declarations, excluding self and transitive axiom dependencies.
fn try_lookup_for_axiom(
    env: &Environment,
    tc: &TypeChecker<'_>,
    name: &Name,
    type_: &Expr,
) -> Option<(String, ConstantKind)> {
    let goal_levels: Vec<Level> = match type_.get_app_fn().kind() {
        ExprKind::Const(_, levels) => levels.iter().cloned().collect(),
        _ => Vec::new(),
    };

    for info in env.constants() {
        if info.name == *name || info.kind == ConstantKind::Axiom {
            continue;
        }
        if let Some(deps) = env.axiom_deps(&info.name) {
            if deps.contains(name) {
                continue;
            }
        }
        let levels = if info.level_params.len() == goal_levels.len() {
            goal_levels.clone()
        } else {
            info.level_params
                .iter()
                .cloned()
                .map(Level::param)
                .collect()
        };
        let Some(cand_type) = env.instantiate_type(&info.name, &levels) else {
            continue;
        };
        if !tc.is_def_eq(&cand_type, type_) {
            continue;
        }
        let candidate = Expr::const_(info.name.clone(), levels);
        if try_verify_proof(env, type_, &candidate) {
            return Some((info.name.to_string(), info.kind));
        }
    }
    None
}

/// Run the full scan across all axioms using refl, trivial_prop, and lookup.
fn run_full_scan(env: &Environment) -> FullScanResults {
    let all_axioms = collect_domain_axioms(env);
    let total = all_axioms.len();
    eprintln!("\n=== FULL SCAN ({total} axioms): refl + trivial_prop + genuine lookup ===\n");

    let mut results = FullScanResults {
        found_refl: Vec::new(),
        found_trivial: Vec::new(),
        found_lookup: Vec::new(),
        not_found: Vec::new(),
    };
    let tc = TypeChecker::with_mode(env, env.mode());

    for (idx, (name, type_)) in all_axioms.iter().enumerate() {
        if idx % 10 == 0 {
            eprintln!("  [{idx}/{total}] scanning {name}...");
        }
        if let Some((strategy, _)) = try_targeted_proof(env, type_) {
            match strategy {
                "refl" => results.found_refl.push(name.to_string()),
                "trivial_prop" => results.found_trivial.push(name.to_string()),
                _ => {}
            }
            eprintln!("  FOUND via {strategy}: {name}");
            continue;
        }
        if let Some((matching, kind)) = try_lookup_for_axiom(env, &tc, name, type_) {
            eprintln!("  FOUND via lookup: {name} (matches {matching} [{kind:?}])");
            results
                .found_lookup
                .push((name.to_string(), matching, kind));
        } else {
            results.not_found.push(name.to_string());
        }
    }
    results
}

/// Print summary of full scan results.
fn print_full_scan_summary(results: &FullScanResults) {
    let total = results.found_refl.len()
        + results.found_trivial.len()
        + results.found_lookup.len()
        + results.not_found.len();
    let found = results.found_refl.len() + results.found_trivial.len() + results.found_lookup.len();

    eprintln!("\n=== FULL SCAN SUMMARY ===");
    eprintln!("Total NNVerify axioms: {total}");
    eprintln!(
        "Auto-provable:        {found} (refl={}, trivial={}, lookup={})",
        results.found_refl.len(),
        results.found_trivial.len(),
        results.found_lookup.len()
    );
    eprintln!("Remaining:            {}", total - found);

    for (label, items) in [
        ("FREE WINS via refl", &results.found_refl),
        ("FREE WINS via trivial_prop", &results.found_trivial),
    ] {
        if !items.is_empty() {
            eprintln!("\n=== {label} ===");
            for name in items {
                eprintln!("  {name}");
            }
        }
    }
    if !results.found_lookup.is_empty() {
        eprintln!("\n=== GENUINE LOOKUP MATCHES ===");
        for (axiom, matching, kind) in &results.found_lookup {
            eprintln!("  {axiom} <=> {matching} [{kind:?}]");
        }
    }
}

/// Full scan with genuine lookup: runs on a dedicated thread with 512MB stack.
/// Tries all three strategies (refl, trivial_prop, lookup-with-transitive-
/// dependency-filtering).
///
/// The lookup strategy is expensive and may stack-overflow on environments with
/// deeply nested types. Each axiom's lookup calls `is_def_eq` against every
/// non-axiom constant, and `axiom_deps` for transitive dependency checking.
///
/// NOTE: This test may abort with stack overflow before completing all axioms.
/// The partial results are still valuable.
#[test]
fn test_proof_search_scan_full_with_lookup() {
    let handle = std::thread::Builder::new()
        .name("proof_search_full_scan".to_string())
        .stack_size(512 * 1024 * 1024)
        .spawn(|| {
            let env = init_full_environment();
            let results = run_full_scan(&env);
            print_full_scan_summary(&results);
        })
        .expect("spawn proof search thread");

    handle.join().expect("proof search thread panicked");
}
