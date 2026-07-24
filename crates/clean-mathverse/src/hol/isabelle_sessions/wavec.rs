// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mode `wavec` — AFP-on-AFP topological DAG ordering.
//!
//! A Wave-C entry's base session is provided by ANOTHER AFP entry; its
//! proofs cascade-verify only once that provider entry is itself captured.
//! We compute the provider graph from every AFP ROOT's `session X = BASE +`
//! line, take the transitive closure of the math seed entries (pulling in
//! non-math provider entries too), topo-sort it, and assign each entry a
//! parent heap:
//!
//! - base in {HOL, HOL-Library}      → `ZP-Lib3e`
//! - base one of the six HOL spines  → `ZP-<Spine>` (Wave-B heap)
//! - base provided by AFP entry P    → `ZP-AFP-<P>` (P's captured heap)
//! - base an un-captured HOL-* sess  → `UNRESOLVED:<base>` (honest gap)

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};

use super::root_parse::parse_root_headers_wavec;
use super::{ensure_outdir, join_lines, read_text_py, write_file, IsabelleSessionsError};

/// Bases satisfied directly by the post-Library heap.
const HOL_BASE: &[&str] = &["HOL", "HOL-Library"];

/// The six HOL-* spine sessions and their Wave-B capture heaps.
const SPINE_HEAP: &[(&str, &str)] = &[
    ("HOL-Analysis", "ZP-Analysis"),
    ("HOL-Probability", "ZP-Probability"),
    ("HOL-Algebra", "ZP-Algebra"),
    ("HOL-Number_Theory", "ZP-Number_Theory"),
    ("HOL-Computational_Algebra", "ZP-Computational_Algebra"),
    ("HOL-Complex_Analysis", "ZP-Complex_Analysis"),
];

/// One row of `afp_wave_c_dag.tsv`, in topo (build) order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WaveCRow {
    /// AFP entry name.
    pub entry: String,
    /// Whether the entry was in the math seed list (vs pulled in as a
    /// provider).
    pub in_seed: bool,
    /// The entry's primary session's base session (None when the entry has
    /// no ROOT / no parsable session — printed as Python's `None`).
    pub base: Option<String>,
    /// The AFP entry providing `base`, when there is one.
    pub provider: Option<String>,
    /// Assigned parent heap (`ZP-…` or `UNRESOLVED:…`).
    pub parent_heap: String,
}

/// Planned output of a wavec-mode run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WaveCPlan {
    /// Rows in deterministic topo build order.
    pub rows: Vec<WaveCRow>,
    /// Number of seed entries requested (list length, duplicates included) —
    /// for the summary line.
    pub seed_count: usize,
}

impl WaveCPlan {
    /// Rows whose parent heap is unresolved (honest gaps).
    #[must_use]
    pub fn unresolved(&self) -> Vec<&WaveCRow> {
        self.rows
            .iter()
            .filter(|r| r.parent_heap.starts_with("UNRESOLVED"))
            .collect()
    }
}

/// `(sess_to_entry, entry_prim_base)` scanned from every AFP ROOT, exactly
/// like the Python `_afp_graph` (entries scanned in sorted order; a session
/// name defined by several entries resolves to the last one scanned).
fn afp_graph(
    afp_thys: &Path,
) -> Result<(BTreeMap<String, String>, BTreeMap<String, String>), IsabelleSessionsError> {
    let mut sess_to_entry = BTreeMap::new();
    let mut entry_prim_base = BTreeMap::new();
    for entry in sorted_entry_names(afp_thys)? {
        let root = afp_thys.join(&entry).join("ROOT");
        if !root.is_file() {
            continue;
        }
        let headers = parse_root_headers_wavec(&read_text_py(&root)?);
        for h in &headers {
            sess_to_entry.insert(h.name.clone(), entry.clone());
        }
        let prim = headers.iter().find(|h| h.name == entry).or(headers.first());
        if let Some(prim) = prim {
            entry_prim_base.insert(entry.clone(), prim.parent.clone());
        }
    }
    Ok((sess_to_entry, entry_prim_base))
}

/// `sorted(os.listdir(afp_thys))` — every directory entry name, sorted.
fn sorted_entry_names(afp_thys: &Path) -> Result<Vec<String>, IsabelleSessionsError> {
    let listing = fs_read_dir(afp_thys)?;
    let mut names: Vec<String> = listing
        .iter()
        .filter_map(|p| p.file_name().and_then(|n| n.to_str()).map(str::to_string))
        .collect();
    names.sort();
    Ok(names)
}

fn fs_read_dir(dir: &Path) -> Result<Vec<PathBuf>, IsabelleSessionsError> {
    let listing = std::fs::read_dir(dir).map_err(|source| IsabelleSessionsError::ListDir {
        path: dir.to_path_buf(),
        source,
    })?;
    let mut out = Vec::new();
    for entry in listing {
        let entry = entry.map_err(|source| IsabelleSessionsError::ListDir {
            path: dir.to_path_buf(),
            source,
        })?;
        out.push(entry.path());
    }
    Ok(out)
}

/// Compute the Wave-C transitive-provider closure, topo order, and parent
/// heaps for `seed_entries`.
pub fn plan_wavec(
    afp_thys: &Path,
    seed_entries: &[String],
) -> Result<WaveCPlan, IsabelleSessionsError> {
    let (sess_to_entry, prim_base) = afp_graph(afp_thys)?;

    let provider = |e: &str| -> Option<&String> {
        let base = prim_base.get(e)?;
        let prov = sess_to_entry.get(base)?;
        (prov != e).then_some(prov)
    };
    let parent_heap = |e: &str| -> String {
        let base = prim_base.get(e).map(String::as_str);
        if let Some(base) = base {
            if HOL_BASE.contains(&base) {
                return "ZP-Lib3e".to_string();
            }
            if let Some((_, heap)) = SPINE_HEAP.iter().find(|(s, _)| *s == base) {
                return (*heap).to_string();
            }
        }
        if let Some(prov) = provider(e) {
            return format!("ZP-AFP-{prov}");
        }
        // Python prints the missing base as `None` — kept for parity.
        format!("UNRESOLVED:{}", base.unwrap_or("None"))
    };

    // Transitive closure of the seed entries' providers (stack-driven, like
    // the Python; visit order does not matter — the topo sorts the set).
    let mut closure: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = seed_entries.to_vec();
    while let Some(e) = stack.pop() {
        if !closure.insert(e.clone()) {
            continue;
        }
        if let Some(p) = provider(&e) {
            stack.push(p.clone());
        }
    }

    // Deterministic topo: place an entry once its provider is placed (or it
    // roots); entries placed earlier in the SAME pass count, matching the
    // Python pass semantics. A cycle (should not happen for AFP) appends the
    // remainder in name order.
    let mut remaining: Vec<String> = closure.iter().cloned().collect();
    remaining.sort();
    let mut placed: Vec<String> = Vec::with_capacity(remaining.len());
    let mut placed_set: HashSet<String> = HashSet::new();
    while !remaining.is_empty() {
        let mut progressed = false;
        for e in remaining.clone() {
            let ready = provider(&e).is_none_or(|p| placed_set.contains(p));
            if ready {
                placed_set.insert(e.clone());
                remaining.retain(|x| *x != e);
                placed.push(e);
                progressed = true;
            }
        }
        if !progressed {
            placed.append(&mut remaining);
            break;
        }
    }

    let seed_set: HashSet<&String> = seed_entries.iter().collect();
    let rows = placed
        .into_iter()
        .map(|e| {
            let heap = parent_heap(&e);
            WaveCRow {
                in_seed: seed_set.contains(&e),
                base: prim_base.get(&e).cloned(),
                provider: provider(&e).cloned(),
                parent_heap: heap,
                entry: e,
            }
        })
        .collect();
    Ok(WaveCPlan {
        rows,
        seed_count: seed_entries.len(),
    })
}

/// Write `afp_wave_c_dag.tsv` / `wave_c_order.txt` / `wave_c_unresolved.txt`
/// into `outdir` (created if missing).
pub fn write_wavec(plan: &WaveCPlan, outdir: &Path) -> Result<(), IsabelleSessionsError> {
    ensure_outdir(outdir)?;
    let mut dag =
        String::from("order\tentry\tin_math_seed\tbase_session\tprovider_entry\tparent_heap\n");
    for (i, row) in plan.rows.iter().enumerate() {
        dag.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\n",
            i + 1,
            row.entry,
            u8::from(row.in_seed),
            row.base.as_deref().unwrap_or("None"),
            row.provider.as_deref().unwrap_or("-"),
            row.parent_heap
        ));
    }
    write_file(&outdir.join("afp_wave_c_dag.tsv"), &dag)?;
    let order: Vec<String> = plan.rows.iter().map(|r| r.entry.clone()).collect();
    write_file(&outdir.join("wave_c_order.txt"), &join_lines(&order))?;
    let unresolved: Vec<String> = plan
        .unresolved()
        .iter()
        .map(|r| format!("{}\t{}", r.entry, r.base.as_deref().unwrap_or("None")))
        .collect();
    write_file(
        &outdir.join("wave_c_unresolved.txt"),
        &join_lines(&unresolved),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spine_heap_table_matches_python() {
        assert_eq!(SPINE_HEAP.len(), 6);
        assert!(SPINE_HEAP.contains(&("HOL-Analysis", "ZP-Analysis")));
        assert!(HOL_BASE.contains(&"HOL-Library"));
    }
}
