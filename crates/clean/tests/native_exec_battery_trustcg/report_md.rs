// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The LX0 report's Markdown rendering: the `.md` written beside the JSON
//! report, from the same rows and identity.

use crate::report::{
    counts, top_causes, ConsumerProbe, Identity, Row, CLAIM, DRIVER, GENERATED_BY, OUTCOMES,
};

fn md_cell(s: &str) -> String {
    s.replace('|', "\\|").replace('\n', " ")
}

/// The Markdown section for the PATH consumer probe.
fn probe_md(probe: Option<&ConsumerProbe>) -> String {
    let mut s = String::from("\n## The trust-cg a bare PATH lookup finds\n\n");
    let Some(p) = probe else {
        s.push_str("No `trust-cg` on PATH other than the selected one.\n");
        return s;
    };
    let mut cause: String = p.run.cause.chars().take(400).collect();
    if p.run.cause.chars().count() > 400 {
        cause.push('…');
    }
    s.push_str(&format!(
        "`{}` ({}) on `{}`: **{}**{} — {}\n\nThe measurement above names its consumer \
         explicitly (`CLEAN_TRUST_CG_BIN`). This line is what the lane does with the consumer \
         a user gets by default on the measuring box; it is recorded when minting and never \
         compared against the pins.\n",
        p.path,
        p.version,
        p.program,
        p.run.outcome,
        if p.run.step.is_empty() {
            String::new()
        } else {
            format!(" at `{}`", p.run.step)
        },
        md_cell(&cause)
    ));
    s
}

pub fn render_md(rows: &[Row], id: &Identity, probe: Option<&ConsumerProbe>) -> String {
    let scoped = counts(rows.iter().filter(|r| r.in_scope));
    let other = counts(rows.iter().filter(|r| !r.in_scope));
    let n_scoped = rows.iter().filter(|r| r.in_scope).count();
    let mut s = String::new();
    s.push_str("# LX0(a): the battery through Clean's core and trust-cg\n\n");
    s.push_str(&format!("**CLAIM: {CLAIM}.** Every body that reached trust-cg was licensed `clean-compiler-unvalidated` after the core's self-checks (or kept its `clean-kernel-tv` claim); that grade claims nothing about the body. Runtime: C via cc.\n\n"));
    s.push_str("Design: `designs/2026-09-30-clean-trust-unified-vision.md` §5 M0/LX0(a). Machine-readable twin: `lx0-trustcg-native-battery-2026-09-30.json` beside this file; both are written by `crates/clean/tests/native_exec_battery_trustcg.rs`, which re-measures and refuses drift.\n\n");
    s.push_str("| | |\n|---|---|\n");
    for (k, v) in [
        ("driver", DRIVER.to_owned()),
        (
            "clean sha",
            format!(
                "`{}`{}",
                id.clean_sha,
                if id.clean_tree_dirty {
                    " (dirty tree)"
                } else {
                    ""
                }
            ),
        ),
        (
            "trust-cg",
            format!(
                "{} — `{}` (blake3 `{}`; source {})",
                id.trust_cg_version, id.trust_cg_path, id.trust_cg_blake3, id.trust_cg_source
            ),
        ),
        ("host", id.host.clone()),
        ("cc", id.cc.clone()),
        ("Lean (expected bytes)", id.lean.clone()),
        ("regenerate", format!("`{GENERATED_BY}`")),
    ] {
        s.push_str(&format!("| {k} | {} |\n", md_cell(&v)));
    }
    s.push_str(&format!("\n## Summary — the {n_scoped} in-scope programs (p01_hello + every C-lane BYTE_EQUAL)\n\n| outcome | programs |\n|---|---:|\n"));
    for o in OUTCOMES {
        s.push_str(&format!(
            "| {o} | {} |\n",
            scoped.get(o).copied().unwrap_or(0)
        ));
    }
    let wrong_exit0 = rows
        .iter()
        .filter(|r| r.in_scope && r.trustcg.exit_zero == Some(true))
        .count();
    s.push_str(&format!("\nWRONG_OUTPUT at exit 0: {wrong_exit0}.\n\n## Blocking causes, ranked by programs blocked\n\n| programs | cause (digits and backticked names folded) | examples |\n|---:|---|---|\n"));
    for (cause, names) in top_causes(rows) {
        let examples: Vec<&str> = names.iter().take(6).map(String::as_str).collect();
        s.push_str(&format!(
            "| {} | {} | {} |\n",
            names.len(),
            md_cell(&cause),
            examples.join(", ")
        ));
    }
    s.push_str(&probe_md(probe));
    s.push_str("\n## In-scope programs\n\n| program | C lane | trust-cg lane | step | first blocking cause (verbatim) |\n|---|---|---|---|---|\n");
    for r in rows.iter().filter(|r| r.in_scope) {
        let mut cause: String = r.trustcg.cause.chars().take(240).collect();
        if r.trustcg.cause.chars().count() > 240 {
            cause.push('…');
        }
        s.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            r.name,
            r.c_lane,
            r.trustcg.outcome,
            r.trustcg.step,
            md_cell(&cause)
        ));
    }
    s.push_str("\n## The other battery programs (outside the LX0(a) scope)\n\n| outcome | programs |\n|---|---:|\n");
    for o in OUTCOMES {
        s.push_str(&format!(
            "| {o} | {} |\n",
            other.get(o).copied().unwrap_or(0)
        ));
    }
    s
}
