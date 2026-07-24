// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-owned runtime contract for `clean kernel verify-constructive-claims`.
//!
//! The clap surface for this verb lives in [`super::kernel_verbs`], but the
//! behavior contract itself belongs in `clean-kernel`: conjecture validation,
//! JSON emission, and exit-code mapping all track kernel-owned audit logic.
//! Keeping that here lets the unified `clean` entry point and the deprecated
//! `verify_constructive_claims` compat shim share one implementation contract.

#[cfg(not(feature = "math-overlays"))]
use anyhow::bail;

/// Audit classification produced by [`classify_constructive_claims`].
///
/// Split out from [`run_verify_constructive_claims`] so tests can pin the
/// exit-code mapping without invoking `std::process::exit`.
#[cfg(feature = "math-overlays")]
#[derive(Debug, Clone, PartialEq, Eq)]
enum ConstructiveClaimsOutcome {
    /// All theorems constructive, OR `--allow-empty` + zero theorems.
    /// Maps to exit code 0.
    AllConstructive,
    /// `--allow-empty` was not set and the namespace had zero theorems.
    /// Maps to exit code 4.
    EmptyNamespace,
    /// At least one theorem had a non-foundational axiom closure. The
    /// inner count is `non_constructive_count`. Maps to exit code 1.
    NonConstructive(usize),
}

#[cfg(feature = "math-overlays")]
fn classify_constructive_claims(
    audit: &crate::env::constructive_claims::ConjectureAudit,
    allow_empty: bool,
) -> ConstructiveClaimsOutcome {
    if audit.theorems.is_empty() {
        if allow_empty {
            ConstructiveClaimsOutcome::AllConstructive
        } else {
            ConstructiveClaimsOutcome::EmptyNamespace
        }
    } else if audit.all_constructive {
        ConstructiveClaimsOutcome::AllConstructive
    } else {
        ConstructiveClaimsOutcome::NonConstructive(audit.non_constructive_count)
    }
}

/// Run the unified constructive-claims audit.
///
/// Preserves the historical exit-code contract:
/// - `0`: all theorems constructive, or `--allow-empty` with no theorems
/// - `1`: at least one theorem is non-constructive
/// - `2`: usage error (unknown conjecture)
/// - `3`: conjecture initialization failed
/// - `4`: no theorem matched and `--allow-empty` was not set
#[cfg(feature = "math-overlays")]
pub fn run_verify_constructive_claims(conjecture: &str, allow_empty: bool) -> anyhow::Result<()> {
    use crate::env::constructive_claims::{
        build_audit, conjecture_theorem_prefixes, is_known_conjecture,
    };
    use crate::env::gamma_crown_verify::{init_conjecture, CONJECTURE_IDS};

    if !is_known_conjecture(conjecture) {
        eprintln!(
            "unknown conjecture '{conjecture}'. valid: {}",
            CONJECTURE_IDS.join(", ")
        );
        std::process::exit(2);
    }

    let env = match init_conjecture(conjecture) {
        Ok(env) => env,
        Err(msg) => {
            eprintln!("failed to initialize conjecture {conjecture}: {msg}");
            std::process::exit(3);
        }
    };

    let audit = build_audit(conjecture, &env);
    println!("{}", serde_json::to_string_pretty(&audit)?);

    match classify_constructive_claims(&audit, allow_empty) {
        ConstructiveClaimsOutcome::AllConstructive => Ok(()),
        ConstructiveClaimsOutcome::EmptyNamespace => {
            eprintln!(
                "no theorems registered under namespaces {:?} for {conjecture}",
                conjecture_theorem_prefixes(conjecture),
            );
            std::process::exit(4);
        }
        ConstructiveClaimsOutcome::NonConstructive(_) => {
            std::process::exit(1);
        }
    }
}

#[cfg(not(feature = "math-overlays"))]
pub fn run_verify_constructive_claims(_conjecture: &str, _allow_empty: bool) -> anyhow::Result<()> {
    bail!(
        "clean kernel verify-constructive-claims requires the `math-overlays` feature. \
         Rebuild with `cargo build -p clean-cli --features math-overlays` \
         (or the equivalent feature on the `clean` package)."
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(feature = "math-overlays"))]
    #[test]
    fn run_without_math_overlays_returns_feature_gate_error() {
        let err = run_verify_constructive_claims("C008", false)
            .expect_err("handler must refuse to run without `math-overlays`");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("math-overlays"),
            "error message must call out the missing feature; got: {msg}"
        );
    }

    #[cfg(feature = "math-overlays")]
    #[test]
    fn classify_maps_every_audit_shape_to_the_correct_outcome() {
        use crate::env::constructive_claims::{ConjectureAudit, TheoremAudit};

        let empty = ConjectureAudit {
            conjecture: "C008".to_string(),
            theorems: vec![],
            non_constructive_count: 0,
            all_constructive: false,
        };
        assert_eq!(
            classify_constructive_claims(&empty, false),
            ConstructiveClaimsOutcome::EmptyNamespace
        );
        assert_eq!(
            classify_constructive_claims(&empty, true),
            ConstructiveClaimsOutcome::AllConstructive
        );

        let all_ok = ConjectureAudit {
            conjecture: "C002".to_string(),
            theorems: vec![TheoremAudit {
                name: "NNVerify.C002.demo".to_string(),
                closure: vec![],
                is_constructive: true,
            }],
            non_constructive_count: 0,
            all_constructive: true,
        };
        assert_eq!(
            classify_constructive_claims(&all_ok, false),
            ConstructiveClaimsOutcome::AllConstructive
        );
        assert_eq!(
            classify_constructive_claims(&all_ok, true),
            ConstructiveClaimsOutcome::AllConstructive
        );

        let mixed = ConjectureAudit {
            conjecture: "C001".to_string(),
            theorems: vec![
                TheoremAudit {
                    name: "NNVerify.C001.t1".to_string(),
                    closure: vec![],
                    is_constructive: true,
                },
                TheoremAudit {
                    name: "NNVerify.C001.t2".to_string(),
                    closure: vec!["sorry".to_string()],
                    is_constructive: false,
                },
            ],
            non_constructive_count: 1,
            all_constructive: false,
        };
        assert_eq!(
            classify_constructive_claims(&mixed, false),
            ConstructiveClaimsOutcome::NonConstructive(1)
        );
        assert_eq!(
            classify_constructive_claims(&mixed, true),
            ConstructiveClaimsOutcome::NonConstructive(1)
        );
    }

    #[cfg(feature = "math-overlays")]
    #[test]
    fn run_pipeline_on_known_conjecture_produces_valid_outcome() {
        use crate::env::constructive_claims::build_audit;
        use crate::env::gamma_crown_verify::init_conjecture;

        let id = "C002";
        let env = init_conjecture(id).expect("C002 must initialize");
        let audit = build_audit(id, &env);

        let outcome = classify_constructive_claims(&audit, true);
        assert!(
            matches!(
                outcome,
                ConstructiveClaimsOutcome::AllConstructive
                    | ConstructiveClaimsOutcome::EmptyNamespace
                    | ConstructiveClaimsOutcome::NonConstructive(_)
            ),
            "classifier must produce a valid outcome; got {outcome:?} for {id}"
        );

        let expected_all_ok =
            !audit.theorems.is_empty() && audit.theorems.iter().all(|t| t.is_constructive);
        assert_eq!(
            audit.all_constructive, expected_all_ok,
            "build_audit invariant broken: all_constructive ({}) != computed ({})",
            audit.all_constructive, expected_all_ok,
        );
    }
}
