// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mode `spine` — the six HOL-* Wave-B spine capture heaps, split
//! Library-style.
//!
//! The spine sessions the Wave-B AFP entries chain on are captured the SAME
//! way the Library was: re-elaborate the spine's own theories on a parent ZP
//! heap under `record_proofs=4`, split into `<= cap`-theory chained
//! sub-sessions so cumulative record-proof RSS resets at every checkpoint
//! (the Lib3 lesson). The heaps chain per the REAL Isabelle HOL session DAG
//! (measured from `$ISABELLE_HOME/src/HOL/ROOT`); a `@<Spine>` first-parent
//! means "chain the first chunk on that upstream spine's LAST captured
//! chunk", keeping the whole wave one linear buildable chain.

use std::path::Path;

use super::afp::{sorted_unique_prefixes, write_manifest};
use super::root_parse::{entry_theories_topo, TheoryWalk};
use super::{
    ensure_outdir, join_lines, py_repr, write_file, IsabelleSessionsError, ManifestRow,
    SessionFragment,
};

/// `(spine_session, src_subdir, first_parent)` rows, exactly the Python
/// `SPINE_SPEC`. `first_parent` is a literal ZP heap or `@<Spine>`.
pub const SPINE_SPEC: &[(&str, &str, &str)] = &[
    (
        "HOL-Computational_Algebra",
        "Computational_Algebra",
        "ZP-Lib3e",
    ),
    (
        "HOL-Number_Theory",
        "Number_Theory",
        "@HOL-Computational_Algebra",
    ),
    ("HOL-Algebra", "Algebra", "@HOL-Computational_Algebra"),
    ("HOL-Analysis", "Analysis", "ZP-Lib3e"),
    ("HOL-Complex_Analysis", "Complex_Analysis", "@HOL-Analysis"),
    ("HOL-Probability", "Probability", "@HOL-Analysis"),
];

/// Planned output of a spine-mode run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpinePlan {
    /// `ROOT.<session>` fragments in emit order.
    pub fragments: Vec<SessionFragment>,
    /// `manifest.tsv` rows (source column = spine session).
    pub manifest: Vec<ManifestRow>,
    /// Session names in chain-respecting build order.
    pub order: Vec<String>,
    /// `WARN: …` diagnostics for skipped spines.
    pub warnings: Vec<String>,
    /// spine session → its final chunk session (the Wave-B parent heap),
    /// in completion order.
    pub spine_last: Vec<(String, String)>,
}

impl SpinePlan {
    /// Total theories across all emitted chunks.
    #[must_use]
    pub fn theories_total(&self) -> usize {
        self.manifest.iter().map(|m| m.n_theories).sum()
    }
}

/// `ZP-<Spine>[-k]` with the `HOL-` prefix dropped.
fn spine_sess_name(sname: &str, k: usize, n: usize) -> String {
    let short = sname.strip_prefix("HOL-").unwrap_or(sname);
    if n == 1 {
        format!("ZP-{short}")
    } else {
        format!("ZP-{short}-{k}")
    }
}

/// Plan the checkpointed fragments for the six HOL-* Wave-B spine heaps.
pub fn plan_spine(hol_src: &Path, cap: usize) -> Result<SpinePlan, IsabelleSessionsError> {
    if cap == 0 {
        return Err(IsabelleSessionsError::ZeroCap);
    }
    let mut plan = SpinePlan {
        fragments: Vec::new(),
        manifest: Vec::new(),
        order: Vec::new(),
        warnings: Vec::new(),
        spine_last: Vec::new(),
    };
    for (sname, subdir, first_parent) in SPINE_SPEC {
        let parent = match first_parent.strip_prefix('@') {
            Some(upstream) => plan
                .spine_last
                .iter()
                .find(|(s, _)| s == upstream)
                .map(|(_, last)| last.clone())
                .ok_or_else(|| IsabelleSessionsError::MissingUpstreamSpine {
                    spine: (*sname).to_string(),
                    upstream: upstream.to_string(),
                })?,
            None => (*first_parent).to_string(),
        };
        let thys = entry_theories_topo(&hol_src.join(subdir), TheoryWalk::TopLevelOnly)?;
        if thys.is_empty() {
            plan.warnings.push(format!(
                "WARN: no theories under {}/{subdir} (skipped)",
                hol_src.display()
            ));
            continue;
        }
        let chunks: Vec<&[String]> = thys.chunks(cap).collect();
        let n = chunks.len();
        let mut prev = parent;
        for (idx, chunk) in chunks.iter().enumerate() {
            let k = idx + 1;
            let sess = spine_sess_name(sname, k, n);
            let contents = fragment_text(sname, &prev, &sess, cap, k, n, chunk);
            plan.fragments.push(SessionFragment {
                session: sess.clone(),
                contents,
            });
            plan.manifest.push(ManifestRow {
                session: sess.clone(),
                source: (*sname).to_string(),
                parent: prev.clone(),
                n_theories: chunk.len(),
                capture_prefix: format!("{sname}."),
            });
            plan.order.push(sess.clone());
            prev = sess;
        }
        plan.spine_last.push(((*sname).to_string(), prev));
    }
    Ok(plan)
}

/// Header + session stanza for one spine chunk — structurally the Python
/// `_SPINE_HEADER` / `_SPINE_SESSION` templates, with the header now crediting
/// the Rust generator (`clean mathverse isabelle-sessions`).
fn fragment_text(
    sname: &str,
    parent: &str,
    sess: &str,
    cap: usize,
    k: usize,
    n: usize,
    chunk: &[String],
) -> String {
    let thy_lines = chunk
        .iter()
        .map(|t| format!("    \"{sname}.{t}\""))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        r#"(* corpus v4 (AFP Wave-B spine) — auto-generated by clean mathverse isabelle-sessions.
   DO NOT EDIT BY HAND. Re-elaborates the HOL-* spine session {sname_repr} on the
   captured heap {parent_repr} under record_proofs=4 so the baked zproof hook
   captures {sname}.<thy>.jsonl. Library-style checkpointing: <= {cap} theories
   per Poly/ML process (RSS resets at each session boundary — the Lib3 lesson).
   Wave-B AFP entries then chain on this spine's LAST chunk (see spine_heaps.tsv).
   See docs/analysis/zproof-afp-staging.md §B. *)
session "{sess}" = "{parent}" +
  description "corpus v4 spine {sname} slice {k}/{n} (chained on {parent})."
  options [quick_and_dirty = false, record_proofs = 4, parallel_limit = 200]
  sessions
    "{sname}"
  theories
{thy_lines}
"#,
        sname_repr = py_repr(sname),
        parent_repr = py_repr(parent),
    )
}

/// Write the planned fragments plus `manifest.tsv` / `sessions.txt` /
/// `prefixes.txt` / `spine_heaps.tsv` into `outdir` (created if missing).
pub fn write_spine(plan: &SpinePlan, outdir: &Path) -> Result<(), IsabelleSessionsError> {
    ensure_outdir(outdir)?;
    for frag in &plan.fragments {
        write_file(
            &outdir.join(format!("ROOT.{}", frag.session)),
            &frag.contents,
        )?;
    }
    write_manifest(&plan.manifest, "spine", outdir)?;
    write_file(&outdir.join("sessions.txt"), &join_lines(&plan.order))?;
    write_file(
        &outdir.join("prefixes.txt"),
        &join_lines(&sorted_unique_prefixes(&plan.manifest)),
    )?;
    let mut heaps = String::from("spine_session\tparent_heap_for_waveB\n");
    for (sname, _, _) in SPINE_SPEC {
        if let Some((_, last)) = plan.spine_last.iter().find(|(s, _)| s == sname) {
            heaps.push_str(&format!("{sname}\t{last}\n"));
        }
    }
    write_file(&outdir.join("spine_heaps.tsv"), &heaps)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spine_sess_name_drops_hol_prefix() {
        assert_eq!(spine_sess_name("HOL-Analysis", 3, 9), "ZP-Analysis-3");
        assert_eq!(
            spine_sess_name("HOL-Complex_Analysis", 1, 1),
            "ZP-Complex_Analysis"
        );
    }

    #[test]
    fn test_spine_spec_matches_python_table() {
        assert_eq!(SPINE_SPEC.len(), 6);
        assert_eq!(SPINE_SPEC[0].2, "ZP-Lib3e");
        assert_eq!(SPINE_SPEC[1].2, "@HOL-Computational_Algebra");
        assert_eq!(SPINE_SPEC[4].2, "@HOL-Analysis");
    }
}
