// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Human / CSV / LaTeX formatters for `VerificationReport`.
//!
//! Split from `gamma_crown_verify.rs` to keep both files under the 500-line
//! soft limit. Part of #3502 honesty rewrite.
//!
//! All three formatters use the honest classification (`proof_mechanism`,
//! `fully_constructive`, `scaffolded`). Only `VERIFIED_CONSTRUCTIVE` results
//! are labeled "Proved" — `VERIFIED_SCAFFOLDED` and `VERIFIED_MIXED` are
//! explicitly disclosed as sorry-inhabited.

use super::gamma_crown_verify::{ConjectureResult, VerificationReport};

/// Aggregate status counts derived from the per-conjecture results.
///
/// The `VerificationReport` struct no longer carries separate
/// `constructive_conjectures`, `mixed_conjectures`, `scaffolded_conjectures`,
/// or `axiom_dependent_conjectures` fields after the cca527072 revert
/// (see #3506). These counts are derived from `report.conjectures` by
/// scanning each `status` string so the formatter output is still honest.
struct StatusCounts {
    constructive: usize,
    hypothesis_wrapped: usize,
    mixed: usize,
    scaffolded: usize,
    axiom_dependent: usize,
}

impl StatusCounts {
    fn from_report(report: &VerificationReport) -> Self {
        let mut c = Self {
            constructive: 0,
            hypothesis_wrapped: 0,
            mixed: 0,
            scaffolded: 0,
            axiom_dependent: 0,
        };
        for result in &report.conjectures {
            match result.status.as_str() {
                "VERIFIED_CONSTRUCTIVE" => c.constructive += 1,
                "VERIFIED_HYPOTHESIS_WRAPPED" => c.hypothesis_wrapped += 1,
                "VERIFIED_MIXED" => c.mixed += 1,
                "VERIFIED_SCAFFOLDED" => c.scaffolded += 1,
                "VERIFIED_AXIOM_DEPENDENT" => c.axiom_dependent += 1,
                _ => {}
            }
        }
        c
    }
}

/// Honest proof-mechanism label for a conjecture, read DIRECTLY from the
/// per-conjecture `proof_mechanism` field (derived by `gamma_crown_verify.rs`
/// from the full transitive axiom closure of the headline theorems, #3700).
/// Previously this was a hand-maintained per-id table that drifted from the
/// kernel-derived verdict; reading the honest field keeps the disclosure
/// consistent with the report itself.
fn conjecture_proof_mechanism_label(c: &ConjectureResult) -> &str {
    &c.proof_mechanism
}

/// Format the report as a human-readable table.
pub fn format_human_report(report: &VerificationReport) -> String {
    let mut out = String::new();
    out.push_str("======================================================================\n");
    out.push_str("       Gamma-Crown Formal Verification Report -- clean kernel\n");
    out.push_str("======================================================================\n\n");
    out.push_str(&format!(
        "Total verification time: {:.1}ms\n\n",
        report.total_verification_time_ms
    ));
    append_human_summary(&mut out, report);
    append_human_per_conjecture_table(&mut out, report);
    append_human_axiom_details(&mut out, report);
    append_human_failed(&mut out, report);
    append_human_scaffolded_disclosure(&mut out, report);
    append_human_final_result(&mut out, report);
    out
}

/// Append the honest four-bucket summary block to `out`. Ordering mirrors
/// the JSON schema; legacy `fully_constructive` is surfaced last so it
/// cannot be mistaken for the publishable count.
fn append_human_summary(out: &mut String, report: &VerificationReport) {
    let counts = StatusCounts::from_report(report);
    out.push_str("-- Summary ----------------------------------------------------------\n");
    out.push_str(&format!(
        "  Conjectures kernel type-checked: {}/{}\n",
        report.conjectures_verified, report.total_conjectures
    ));
    out.push_str(&format!(
        "  Proved (constructive):           {}  (full closure ⊆ foundations)\n",
        counts.constructive
    ));
    out.push_str(&format!(
        "  Hypothesis-wrapped (H->H):       {}  (claim taken as a local premise)\n",
        counts.hypothesis_wrapped
    ));
    out.push_str(&format!(
        "  Mixed (partial scaffolding):     {}  (some theorems sorry-inhabited)\n",
        counts.mixed
    ));
    out.push_str(&format!(
        "  Scaffolded (sorry-inhabited):    {}  (headline closure reaches @sorry)\n",
        counts.scaffolded
    ));
    out.push_str(&format!(
        "  Axiom-dependent:                 {}  (full closure reaches a domain axiom)\n",
        counts.axiom_dependent
    ));
    out.push_str(&format!(
        "  Total theorems:                  {}\n",
        report.total_theorems
    ));
    out.push_str(&format!(
        "  Namespace axioms (informational):{}\n\n",
        report.total_domain_axioms
    ));
}

/// Append the per-conjecture fixed-width table. Status column maps the
/// JSON status string to the five-character label used in the table
/// (PROVED / MIXED / SCAFF / FORMAL / FAILED / UNKNOWN).
fn append_human_per_conjecture_table(out: &mut String, report: &VerificationReport) {
    out.push_str("-- Per-Conjecture Results -------------------------------------------\n");
    out.push_str("  Status legend: PROVED = constructive proof term (publishable)\n");
    out.push_str("                 HYPWRP = H->H projection; claim taken as a local premise\n");
    out.push_str("                 MIXED  = zero domain axioms, some claims sorry-inhabited\n");
    out.push_str("                 SCAFF  = headline closure reaches sorry/sorryAx\n");
    out.push_str("                 FORMAL = full closure reaches a domain axiom\n\n");
    out.push_str(&format!(
        "{:<6} {:<42} {:>6} {:>5} {:>5} {:>5} {:<8} {:>8}\n",
        "ID", "Description", "Axioms", "Thms", "Defs", "Opqs", "Status", "Time(ms)"
    ));
    out.push_str(&format!("{}\n", "-".repeat(92)));
    for c in &report.conjectures {
        let status_short = match c.status.as_str() {
            "VERIFIED_CONSTRUCTIVE" => "PROVED",
            "VERIFIED_HYPOTHESIS_WRAPPED" => "HYPWRP",
            "VERIFIED_MIXED" => "MIXED",
            "VERIFIED_SCAFFOLDED" => "SCAFF",
            "VERIFIED_AXIOM_DEPENDENT" => "FORMAL",
            "INIT_FAILED" => "FAILED",
            _ => "UNKNOWN",
        };
        let desc = if c.description.len() > 42 {
            format!("{}...", &c.description[..39])
        } else {
            c.description.clone()
        };
        out.push_str(&format!(
            "{:<6} {:<42} {:>6} {:>5} {:>5} {:>5} {:<8} {:>8.1}\n",
            c.id,
            desc,
            c.domain_axioms,
            c.theorems,
            c.definitions,
            c.opaques,
            status_short,
            c.verification_time_ms,
        ));
    }
    out.push_str(&format!("{}\n", "-".repeat(92)));
}

/// Append the remaining-domain-axioms section (present iff ≥1 conjecture
/// still has `Declaration::Axiom` entries under a conjecture namespace).
fn append_human_axiom_details(out: &mut String, report: &VerificationReport) {
    let axiom_dependent: Vec<&ConjectureResult> = report
        .conjectures
        .iter()
        .filter(|c| c.domain_axioms > 0)
        .collect();
    if axiom_dependent.is_empty() {
        return;
    }
    out.push_str("\n-- Remaining Domain Axioms -----------------------------------------\n");
    for c in &axiom_dependent {
        let nn_axioms: Vec<&String> = c
            .axiom_names
            .iter()
            .filter(|n| n.starts_with("NNVerify.") || n.starts_with("NNVerification."))
            .collect();
        if !nn_axioms.is_empty() {
            out.push_str(&format!("  {} ({} axioms):\n", c.id, nn_axioms.len()));
            for name in &nn_axioms {
                out.push_str(&format!("    - {name}\n"));
            }
        }
    }
}

/// Append the failed-conjectures section (init-time failures only).
fn append_human_failed(out: &mut String, report: &VerificationReport) {
    let failed: Vec<&ConjectureResult> = report.conjectures.iter().filter(|c| !c.init_ok).collect();
    if failed.is_empty() {
        return;
    }
    out.push_str("\n-- Failed Conjectures -----------------------------------------------\n");
    for c in &failed {
        out.push_str(&format!(
            "  {}: {}\n",
            c.id,
            c.error.as_deref().unwrap_or("unknown error")
        ));
    }
}

/// Append the scaffolded / mixed conjectures disclosure block. This is
/// the #3502 honesty section: it calls out every conjecture that passes
/// type checking with zero axioms but carries sorry-inhabited Opaques.
fn append_human_scaffolded_disclosure(out: &mut String, report: &VerificationReport) {
    let scaffolded: Vec<&ConjectureResult> = report
        .conjectures
        .iter()
        .filter(|c| c.status == "VERIFIED_SCAFFOLDED" || c.status == "VERIFIED_MIXED")
        .collect();
    if scaffolded.is_empty() {
        return;
    }
    out.push_str("\n-- Scaffolded / Mixed Conjectures (sorry-inhabited) -----------------\n");
    out.push_str("  These conjectures pass kernel type checking with zero remaining\n");
    out.push_str("  Declaration::Axiom entries, BUT one or more claim-level Opaques\n");
    out.push_str("  have bodies built from `@sorry` (sorry-inhabited). They are NOT\n");
    out.push_str("  constructive proofs and MUST NOT be labeled 'Proved' per the\n");
    out.push_str("  repository's Proof Soundness Rules (design doc).\n");
    out.push_str("  See data/axiom_audit.json `proof_mechanism` field and\n");
    out.push_str("  reports/audit/2026-04-19-auditor-round4.md.\n\n");
    for c in &scaffolded {
        let kind = if c.status == "VERIFIED_MIXED" {
            "MIXED"
        } else {
            "SCAFFOLDED"
        };
        out.push_str(&format!(
            "  {} ({}): proof_mechanism={}\n",
            c.id,
            kind,
            conjecture_proof_mechanism_label(c)
        ));
    }
}

/// Append the final RESULT line summarising all buckets.
fn append_human_final_result(out: &mut String, report: &VerificationReport) {
    let counts = StatusCounts::from_report(report);
    out.push('\n');
    if report.conjectures_failed == 0 {
        out.push_str(&format!(
            "RESULT: {} / {} conjectures kernel type-checked\n",
            report.conjectures_verified, report.total_conjectures
        ));
        out.push_str(&format!(
            "        {} constructive, {} hypothesis-wrapped, {} mixed, {} scaffolded, {} axiom-dependent\n",
            counts.constructive,
            counts.hypothesis_wrapped,
            counts.mixed,
            counts.scaffolded,
            counts.axiom_dependent,
        ));
    } else {
        out.push_str(&format!(
            "RESULT: {} FAILED ({} verified)\n",
            report.conjectures_failed, report.conjectures_verified
        ));
    }
}

/// Format the report as a CSV table. Columns include the honest
/// classification fields: `fully_constructive`, `scaffolded`,
/// `proof_mechanism`. The legacy `constructive_legacy` column (zero live
/// axioms) is retained for back-compat but should NOT be used as the
/// publishable-proof indicator — prefer `fully_constructive`.
pub fn format_csv_report(report: &VerificationReport) -> String {
    let mut out = String::new();
    out.push_str(
        "id,description,status,domain_axioms,theorems,definitions,opaques,\
         constructive_legacy,fully_constructive,scaffolded,proof_mechanism,\
         verification_time_ms\n",
    );
    for c in &report.conjectures {
        let desc = if c.description.contains(',') || c.description.contains('"') {
            format!("\"{}\"", c.description.replace('"', "\"\""))
        } else {
            c.description.clone()
        };
        // #3700: read the honest `proof_mechanism` directly from the result
        // (kernel-derived from the full headline closure). `fully_constructive`
        // is true only for the genuinely-constructive status.
        let full_constructive = c.status == "VERIFIED_CONSTRUCTIVE";
        let scaffolded = matches!(c.status.as_str(), "VERIFIED_MIXED" | "VERIFIED_SCAFFOLDED");
        let mechanism = conjecture_proof_mechanism_label(c);
        out.push_str(&format!(
            "{},{},{},{},{},{},{},{},{},{},{},{:.1}\n",
            c.id,
            desc,
            c.status,
            c.domain_axioms,
            c.theorems,
            c.definitions,
            c.opaques,
            c.constructive,
            full_constructive,
            scaffolded,
            mechanism,
            c.verification_time_ms,
        ));
    }
    out
}

/// Format the report as a LaTeX table. Status labels follow the honest
/// classification: `Proved` is reserved for real constructive proofs only.
/// Sorry-inhabited Opaques are labeled `Scaffolded`, partially-scaffolded
/// conjectures are labeled `Mixed`, and conjectures with remaining
/// `Declaration::Axiom` entries are labeled `Formal`.
pub fn format_latex_report(report: &VerificationReport) -> String {
    let mut out = String::new();
    out.push_str("% Gamma-Crown Formal Verification Results\n");
    out.push_str(&format!(
        "% Total verification time: {:.1}ms\n",
        report.total_verification_time_ms
    ));
    out.push_str("% Honesty note (see #3502, data/axiom_audit.json `proof_mechanism`):\n");
    out.push_str("%   Proved     = every claim is a real proof term (zero sorry, zero axioms).\n");
    out.push_str(
        "%   Mixed      = zero domain axioms, but >=1 claim Opaque is @sorry-inhabited.\n",
    );
    out.push_str("%   Scaffolded = zero domain axioms, ALL claim Opaques are @sorry-inhabited.\n");
    out.push_str("%   Formal     = kernel type-checked, Declaration::Axiom remains.\n");
    out.push_str("\\begin{table}[t]\n");
    out.push_str("\\centering\n");
    out.push_str("\\caption{Gamma-Crown conjecture verification status. ``Proved'' indicates\n");
    out.push_str("  a real constructive proof term whose transitive axiom closure is contained\n");
    out.push_str("  in the foundational set. ``Mixed'' and ``Scaffolded'' indicate conjectures\n");
    out.push_str("  that pass kernel type checking with zero domain axioms but contain one or\n");
    out.push_str("  more claim-level Opaques inhabited by \\texttt{@sorry} -- logically vacuous\n");
    out.push_str("  placeholders pending derivation. ``Formal'' indicates kernel-accepted with\n");
    out.push_str("  remaining \\texttt{Declaration::Axiom} entries. Only ``Proved'' counts as a\n");
    out.push_str("  formal proof for publication purposes.}\n");
    out.push_str("\\label{tab:gamma-crown-verification}\n");
    out.push_str("\\begin{tabular}{llrrrrl}\n");
    out.push_str("\\toprule\n");
    out.push_str("ID & Description & Axioms & Thms & Defs & Opqs & Status \\\\\n");
    out.push_str("\\midrule\n");

    for c in &report.conjectures {
        let status = match c.status.as_str() {
            "VERIFIED_CONSTRUCTIVE" => "\\textbf{Proved}",
            "VERIFIED_HYPOTHESIS_WRAPPED" => "Hyp-wrap",
            "VERIFIED_MIXED" => "Mixed",
            "VERIFIED_SCAFFOLDED" => "Scaffolded",
            "VERIFIED_AXIOM_DEPENDENT" => "Formal",
            _ if c.init_ok => "Unknown",
            _ => "Failed",
        };
        let desc = c
            .description
            .replace('_', "\\_")
            .replace('&', "\\&")
            .replace('%', "\\%");
        out.push_str(&format!(
            "{} & {} & {} & {} & {} & {} & {} \\\\\n",
            c.id, desc, c.domain_axioms, c.theorems, c.definitions, c.opaques, status,
        ));
    }

    let counts = StatusCounts::from_report(report);
    out.push_str("\\midrule\n");
    out.push_str(&format!(
        "\\multicolumn{{7}}{{l}}{{\\small Proved: {} \\quad Mixed: {} \\quad Scaffolded: {} \\quad Formal: {}}} \\\\\n",
        counts.constructive,
        counts.mixed,
        counts.scaffolded,
        counts.axiom_dependent,
    ));
    out.push_str(&format!(
        "\\textbf{{Total}} & {} conjectures & {} & {} & & & {}/{} kernel-verified \\\\\n",
        report.total_conjectures,
        report.total_domain_axioms,
        report.total_theorems,
        report.conjectures_verified,
        report.total_conjectures,
    ));
    out.push_str("\\bottomrule\n");
    out.push_str("\\end{tabular}\n");
    out.push_str("\\end{table}\n");

    out
}
