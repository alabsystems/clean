// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Main `mathverse_try` check pipeline: parse → register → classify.

use std::io::{self, Write};

use clap::Parser;
use clean_kernel::env::is_trust_marker;
use clean_kernel::{Declaration, Environment, Name};

use super::parse::parse_expr;
use super::report::{Report, Status};

#[derive(Parser, Debug)]
#[command(
    name = "mathverse_try",
    version,
    about = "Kernel sketchpad: check a proof term against a goal + axiom closure",
    long_about = None,
)]
pub(super) struct Args {
    /// Goal proposition (s-expression, see module docs).
    #[arg(long)]
    pub goal: String,

    /// Proof term (s-expression, see module docs).
    #[arg(long)]
    pub proof: String,

    /// Environment seed: `none` (default) or `seed-native`.
    ///
    /// `seed-native` registers the same Tier A lemmas + CROWN +
    /// interval-arith / IBP theorems used by `mathverse_shard build-native`,
    /// so new proof sketches can reference them by name.
    #[arg(long, default_value = "none")]
    pub env: String,

    /// Optional name for the attempted theorem (default `__try__`).
    #[arg(long, default_value = "__try__")]
    pub name: String,

    /// Emit JSON output.
    #[arg(long, default_value_t = false)]
    pub json: bool,
}

/// Parse → seed → register → classify. Kept under 80 lines so each
/// stage stays visible at a glance; see helpers below for the details.
pub(super) fn run(args: &Args) -> Report {
    let mut report = Report::default();

    let goal = match parse_expr(&args.goal) {
        Ok(e) => e,
        Err(e) => {
            report.error = Some(format!("goal parse error: {e}"));
            return report;
        }
    };
    let proof = match parse_expr(&args.proof) {
        Ok(e) => e,
        Err(e) => {
            report.error = Some(format!("proof parse error: {e}"));
            return report;
        }
    };

    let env = match build_env(&args.env) {
        Ok(e) => e,
        Err(err) => {
            report.error = Some(err);
            return report;
        }
    };
    let mut env = env;

    let name = Name::from_string(&args.name);
    if env.get_const(&name).is_some() {
        report.error = Some(format!(
            "theorem name `{}` already exists in seeded environment — pick another via --name",
            args.name
        ));
        return report;
    }

    // Full kernel type check — this is the whole point of the tool.
    let decl = Declaration::Theorem {
        name: name.clone(),
        level_params: Vec::new(),
        type_: goal,
        value: proof,
    };
    if let Err(e) = env.add_decl(decl) {
        report.error = Some(format!("kernel rejected: {e}"));
        return report;
    }

    report.status = Status::Pass;
    populate_success(&env, &name, &mut report);
    report
}

fn build_env(kind: &str) -> Result<Environment, String> {
    let mut env = Environment::new();
    match kind {
        "none" => Ok(env),
        "seed-native" => {
            let warnings = seed_native(&mut env);
            emit_warnings(&warnings);
            Ok(env)
        }
        other => Err(format!(
            "unknown --env value `{other}` (expected `none` or `seed-native`)"
        )),
    }
}

fn emit_warnings(warnings: &[String]) {
    if warnings.is_empty() {
        return;
    }
    let stderr = io::stderr();
    let mut err = stderr.lock();
    for w in warnings {
        let _ = writeln!(err, "warning: {w}");
    }
}

fn populate_success(env: &Environment, name: &Name, report: &mut Report) {
    if let Some(info) = env.get_const(name) {
        report.inferred_type = Some(format!("{}", info.type_));
    }
    if let Some(deps) = env.axiom_deps(name) {
        split_deps(deps.into_iter().map(|n| n.to_string()), report);
    }
}

fn split_deps<I: Iterator<Item = String>>(names: I, report: &mut Report) {
    let mut all: Vec<String> = names.collect();
    all.sort();
    let (trust, axioms): (Vec<_>, Vec<_>) = all
        .into_iter()
        .partition(|n| is_trust_marker(&Name::from_string(n)));
    report.axiom_closure = axioms;
    report.trust_markers = trust;
}

/// Mirror of `mathverse_shard build-native`'s `seed_environment` (see
/// `src/bin/mathverse_shard/native_build.rs`). Kept in lockstep so that a
/// proof passing `mathverse_try --env seed-native` will also land in the
/// clean-Native shard when copied into a `nn_verify_tier_a_*.rs` file.
fn seed_native(env: &mut Environment) -> Vec<String> {
    let mut warnings = Vec::new();
    macro_rules! try_init {
        ($call:expr, $tag:literal) => {
            if let Err(e) = $call {
                warnings.push(format!("{}: {e}", $tag));
            }
        };
    }
    try_init!(
        env.init_nn_verify_blockwise_crown_ext(),
        "blockwise_crown_ext"
    );
    try_init!(env.init_nn_verify_interval_arith_proofs(), "interval_arith");
    try_init!(env.init_nn_verify_ibp_width_zero(), "ibp_width_zero");
    try_init!(env.init_nn_verify_tier_a_rat_min_zero(), "rat_min_zero");
    try_init!(
        env.init_nn_verify_tier_a_rat_le_refl_zero(),
        "rat_le_refl_zero"
    );
    try_init!(
        env.init_nn_verify_tier_a_rat_zero_eq_max(),
        "rat_zero_eq_max"
    );
    try_init!(
        env.init_nn_verify_tier_a_rat_zero_eq_min(),
        "rat_zero_eq_min"
    );
    try_init!(env.init_nn_verify_tier_a_rat_max_eq_min(), "rat_max_eq_min");
    try_init!(env.init_nn_verify_tier_a_rat_min_eq_max(), "rat_min_eq_max");
    try_init!(
        env.init_nn_verify_tier_a_rat_max_zero_zero_alt(),
        "rat_max_zero_zero_alt"
    );
    try_init!(
        env.init_nn_verify_tier_a_rat_min_zero_zero_alt(),
        "rat_min_zero_zero_alt"
    );
    try_init!(
        env.init_nn_verify_tier_a_rat_le_refl_max_zero_zero(),
        "rat_le_refl_max_zero_zero"
    );
    try_init!(
        env.init_nn_verify_tier_a_rat_le_refl_min_zero_zero(),
        "rat_le_refl_min_zero_zero"
    );
    warnings
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(goal: &str, proof: &str, seed: &str) -> Args {
        Args {
            goal: goal.to_string(),
            proof: proof.to_string(),
            env: seed.to_string(),
            name: "__test__".to_string(),
            json: false,
        }
    }

    #[test]
    fn test_smoke_rat_min_zero_zero_passes_with_seeded_env() {
        // Verbatim port of `NNVerify.Rat.min_zero_zero` from
        // `crates/clean-kernel/src/env/nn_verify_tier_a_rat_min_zero.rs` —
        // the canonical Tier A "sorry-free Theorem" pattern. Proves the
        // binary works end-to-end on a known-good proof.
        let goal = "(Eq^1 Rat (Rat.min Rat.zero Rat.zero) Rat.zero)";
        let proof = "(Rat.min_def Rat.zero Rat.zero (Rat.le_refl Rat.zero))";
        let rep = run(&args(goal, proof, "seed-native"));
        assert_eq!(rep.status, Status::Pass, "error was: {:?}", rep.error);
        // All three axioms (Rat.min, Rat.min_def, Rat.le_refl) are
        // FOUNDATIONAL_AXIOMS, so the non-foundational closure is
        // empty and the proof is classified as CONSTRUCTIVE.
        assert!(
            rep.axiom_closure.is_empty(),
            "expected empty closure, got: {:?}",
            rep.axiom_closure
        );
        assert_eq!(rep.classification(), "CONSTRUCTIVE");
    }

    #[test]
    fn test_smoke_type_mismatch_is_fail() {
        let goal = "(Eq^1 Rat Rat.zero Rat.zero)";
        let proof = "Rat.zero"; // definitely not a proof of equality
        let rep = run(&args(goal, proof, "seed-native"));
        assert_eq!(rep.status, Status::Fail);
        assert!(rep.error.is_some());
    }

    #[test]
    fn test_parse_error_surfaces_as_fail() {
        let rep = run(&args("(unterminated", "Rat.zero", "none"));
        assert_eq!(rep.status, Status::Fail);
        assert!(
            rep.error
                .as_deref()
                .unwrap_or("")
                .contains("goal parse error"),
            "got: {:?}",
            rep.error
        );
    }

    #[test]
    fn test_unknown_env_surfaces_as_fail() {
        let rep = run(&args("Rat.zero", "Rat.zero", "bogus"));
        assert_eq!(rep.status, Status::Fail);
        assert!(rep
            .error
            .as_deref()
            .unwrap_or("")
            .contains("unknown --env value"));
    }
}
