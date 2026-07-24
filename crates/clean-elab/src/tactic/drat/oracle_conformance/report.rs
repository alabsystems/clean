// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT oracle-conformance report rendering.

use super::{CaseClassification, CaseResult, OracleOutcome, ResolvedOracle};

fn verdict_str(accepted: bool) -> &'static str {
    if accepted {
        "Accept"
    } else {
        "Reject"
    }
}

fn oracle_outcome_str(outcome: &OracleOutcome) -> String {
    match outcome {
        OracleOutcome::Accepted => "Accept".to_string(),
        OracleOutcome::Rejected => "Reject".to_string(),
        OracleOutcome::InvocationError { exit_code } => {
            format!("Error(exit={:?})", exit_code)
        }
    }
}

/// Render the conformance report as Markdown.
pub fn render_report(
    results: &[CaseResult],
    oracles: &[ResolvedOracle],
    command: &str,
    date: &str,
) -> String {
    let mut out = String::new();

    out.push_str("# LRAT Oracle Conformance Report\n\n");
    out.push_str(&format!("**Command:** `{}`\n", command));
    out.push_str(&format!("**Date:** {}\n", date));

    render_oracle_list(&mut out, oracles);
    render_case_matrix(&mut out, results, oracles);
    render_summary(&mut out, results);
    render_error_details(&mut out, results);
    render_next_actions(&mut out, results);

    out
}

fn render_oracle_list(out: &mut String, oracles: &[ResolvedOracle]) {
    if oracles.is_empty() {
        out.push_str("**Oracle(s):** none (internal-only run)\n\n");
    } else {
        out.push_str("**Oracle(s):**\n");
        for oracle in oracles {
            out.push_str(&format!(
                "- `{}` (`{}`)\n",
                oracle.kind,
                oracle.path.display()
            ));
        }
        out.push('\n');
    }
}

fn render_case_matrix(out: &mut String, results: &[CaseResult], oracles: &[ResolvedOracle]) {
    out.push_str("## Per-Case Matrix\n\n");
    out.push_str("| Case | Expected | LratVerifier | StreamingLrat | Checkpoint |");
    for oracle in oracles {
        out.push_str(&format!(" {} |", oracle.kind));
    }
    out.push_str(" Classification |\n");

    out.push_str("|------|----------|-------------|---------------|------------|");
    for _ in oracles {
        out.push_str("--------|");
    }
    out.push_str("----------------|\n");

    for r in results {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |",
            r.name,
            verdict_str(r.expected),
            verdict_str(r.batch_verdict),
            verdict_str(r.streaming_verdict),
            verdict_str(r.checkpoint_verdict),
        ));

        for (_, verdict) in &r.oracle_verdicts {
            out.push_str(&format!(" {} |", oracle_outcome_str(&verdict.outcome)));
        }
        for _ in r.oracle_verdicts.len()..oracles.len() {
            out.push_str(" — |");
        }

        out.push_str(&format!(" {} |\n", r.classification));
    }
}

fn render_summary(out: &mut String, results: &[CaseResult]) {
    out.push_str("\n## Summary\n\n");
    let total = results.len();
    let count = |c: CaseClassification| results.iter().filter(|r| r.classification == c).count();

    out.push_str(&format!("- **Total:** {}\n", total));
    out.push_str(&format!(
        "- **AllAgree:** {}\n",
        count(CaseClassification::AllAgree)
    ));
    out.push_str(&format!(
        "- **InternalDisagreement:** {}\n",
        count(CaseClassification::InternalDisagreement)
    ));
    out.push_str(&format!(
        "- **OracleMismatch:** {}\n",
        count(CaseClassification::OracleMismatch)
    ));
    out.push_str(&format!(
        "- **OracleInvocationError:** {}\n",
        count(CaseClassification::OracleInvocationError)
    ));
    out.push_str(&format!(
        "- **OracleUnavailable:** {}\n",
        count(CaseClassification::OracleUnavailable)
    ));
}

fn render_error_details(out: &mut String, results: &[CaseResult]) {
    let error_cases: Vec<_> = results
        .iter()
        .filter(|r| {
            r.classification == CaseClassification::OracleInvocationError
                || r.classification == CaseClassification::OracleMismatch
        })
        .collect();

    if error_cases.is_empty() {
        return;
    }

    out.push_str("\n## Mismatch / Error Details\n\n");
    for r in error_cases {
        out.push_str(&format!("### {}\n\n", r.name));
        for (kind, verdict) in &r.oracle_verdicts {
            if matches!(
                verdict.outcome,
                OracleOutcome::InvocationError { .. } | OracleOutcome::Rejected
            ) {
                out.push_str(&format!(
                    "**{}:** {}\n",
                    kind,
                    oracle_outcome_str(&verdict.outcome)
                ));
                if !verdict.stderr.is_empty() {
                    out.push_str(&format!("```\n{}\n```\n", verdict.stderr.trim()));
                }
            }
        }
        out.push('\n');
    }
}

fn render_next_actions(out: &mut String, results: &[CaseResult]) {
    let count = |c: CaseClassification| results.iter().filter(|r| r.classification == c).count();
    let internal_disagree = count(CaseClassification::InternalDisagreement);
    let oracle_mismatch = count(CaseClassification::OracleMismatch);
    let oracle_error = count(CaseClassification::OracleInvocationError);
    let oracle_unavail = count(CaseClassification::OracleUnavailable);
    let agree = count(CaseClassification::AllAgree);

    out.push_str("\n## Next Actions\n\n");
    if internal_disagree > 0 {
        out.push_str("- **P0:** Internal disagreement between LratVerifier and StreamingLratVerifier. Investigate immediately.\n");
    }
    if oracle_mismatch > 0 {
        out.push_str("- **P1:** Oracle mismatch detected. Compare clean LRAT semantics against external checker.\n");
    }
    if oracle_error > 0 {
        out.push_str("- Oracle invocation errors. Check oracle binary availability and file format compatibility.\n");
    }
    if oracle_unavail > 0 && agree == 0 {
        out.push_str("- No oracle available. Build `ay-lrat-check` (`cargo build -p ay-lrat-check --release` in ~/ay) or pass `--ay-lrat-check <path>`.\n");
    }
    if internal_disagree == 0 && oracle_mismatch == 0 && oracle_error == 0 {
        out.push_str("(none — all verifiers agree)\n");
    }
}
