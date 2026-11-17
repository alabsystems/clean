// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! Diagnostic DATA replay only. Deserializing an environment does not confer
//! source admission, checked relations, or any object/function proof grade.
//! Enable `clean-kernel/reduction-stats` for reduction-name attribution.

use clean_kernel::{BigNat, Environment, Expr, Level, TypeChecker};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let snapshot = std::fs::read(arguments.next().ok_or("missing environment DATA")?)?;
    let bytes = std::fs::read(arguments.next().ok_or("missing WHOLE original bytes")?)?;
    if arguments.next().is_some() || bytes.is_empty() || bytes.len() > 1024 * 1024 {
        return Err("diagnostic argument or whole-input budget".into());
    }
    let environment = Environment::from_dag_bincode(&snapshot)?;
    let limbs = bytes
        .chunks(8)
        .map(|chunk| {
            let mut limb = [0; 8];
            limb[..chunk.len()].copy_from_slice(chunk);
            u64::from_le_bytes(limb)
        })
        .collect();
    let input = [
        Expr::nat_lit(bytes.len() as u64),
        Expr::bignat_lit(BigNat::from_limbs(limbs)),
    ];
    let source = Expr::apps(
        Expr::const_str("TrustIr.Formula.V2.ConjHoldsB"),
        input.clone(),
    );
    let goal = Expr::apps(Expr::const_str("TrustIr.Formula.V2.GoalB"), input.clone());
    let statement = Expr::apps(Expr::const_str("Iff"), [source, goal]);
    let ready = Expr::apps(
        Expr::const_(
            clean_kernel::Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
    );
    let proof = Expr::apps(
        Expr::const_str("TrustIr.Formula.V2.original_bytes_iff_goal"),
        [input[0].clone(), input[1].clone(), ready],
    );
    let mut checker = TypeChecker::new(&environment);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.enable_heartbeat_profiler();
    clean_kernel::reduction_stats_reset();
    let result = checker
        .infer_sort(&statement)
        .and_then(|_| checker.check_type(&proof, &statement));
    eprintln!(
        "WHOLE INPUT DIAGNOSTIC DATA ONLY: {:?}",
        checker.heartbeat_profile()
    );
    eprintln!("{}", clean_kernel::reduction_stats_report(30));
    result?;
    Ok(())
}
