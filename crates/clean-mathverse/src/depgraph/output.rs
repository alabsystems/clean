// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Output formats for the depgraph analyzer.
//!
//! Three renderings are supported:
//!
//! - **JSON** — machine-readable closure dump for `--headline` and
//!   `--impact`. Uses `serde_json` and preserves `NodeClass` tags.
//! - **Graphviz DOT** — `--graphviz` and the committed
//!   `reports/depgraph/*.dot` artifacts. Node color encodes class so the
//!   rendered graph lets humans eyeball "where does the trust gap live?".
//! - **Ranked text** — `--unblock` stdout + committed
//!   `reports/depgraph/*.txt`. Columns: `impact`, `direct-dependents`,
//!   `class`, `name`. Plain ASCII so the artifact is greppable.
//!
//! The formatters do not touch filesystem — the caller wires them to
//! `std::fs::write` or stdout as appropriate. This keeps the depgraph
//! library usable from tests, scripts, and future web UIs without
//! filesystem side-effects.

use std::fmt::Write;

use crate::depgraph::analyze::{ClosureGraph, NodeClass, UnblockCandidate};

/// Serialize a headline closure as pretty JSON.
///
/// Returns a `String` (UTF-8). Panics only on serde/serialization
/// failures, which cannot happen for the types we construct.
#[must_use]
pub fn emit_headline_json(graph: &ClosureGraph) -> String {
    serde_json::to_string_pretty(graph).expect("ClosureGraph always serializes")
}

/// Render a `ClosureGraph` as a Graphviz DOT digraph.
///
/// Nodes are colored by class:
///
/// | Class | Color |
/// |---|---|
/// | ConstructiveTheorem | `#cfe8cf` (green) |
/// | AxiomDependentTheorem | `#fff2b3` (yellow) |
/// | DomainAxiom | `#f4b6b6` (red) |
/// | FoundationalAxiom | `#e0e0e0` (grey) |
/// | TrustMarker | `#d9b3ff` (purple) |
/// | Definition | `#cce0ff` (blue) |
/// | Unchecked / Missing | `#ffcc80` (orange) |
#[must_use]
pub fn emit_dot(graph: &ClosureGraph) -> String {
    // All `writeln!` calls target a `String` and therefore cannot fail:
    // `fmt::Write` for `String` is infallible (it only allocates).
    let mut s = String::new();
    writeln!(&mut s, "digraph depgraph {{").expect("invariant: write to String");
    writeln!(&mut s, "  rankdir=LR;").expect("invariant: write to String");
    writeln!(
        &mut s,
        "  node [shape=box, style=filled, fontname=\"Helvetica\"];"
    )
    .expect("invariant: write to String");
    writeln!(&mut s, "  graph [fontname=\"Helvetica\"];").expect("invariant: write to String");
    // Label with root + counts for eyeballing.
    let total = graph.nodes.len();
    let domain = graph.domain_axiom_count();
    writeln!(
        &mut s,
        "  labelloc=\"t\"; label=\"depgraph({}) — {} nodes, {} domain-axiom leaves\";",
        dot_escape(&graph.root),
        total,
        domain
    )
    .expect("invariant: write to String");
    // Emit nodes, deterministic order.
    let mut nodes = graph.sorted_nodes();
    // Root first for visual anchor.
    nodes.sort_by(|a, b| {
        let a_root = a.name == graph.root;
        let b_root = b.name == graph.root;
        match (a_root, b_root) {
            (true, false) => std::cmp::Ordering::Less,
            (false, true) => std::cmp::Ordering::Greater,
            _ => a.name.cmp(&b.name),
        }
    });
    for node in &nodes {
        let color = class_color(node.class);
        let class_str = class_label(node.class);
        let label = format!(
            "{}\\n[{}] impact={}",
            dot_escape(&node.name),
            class_str,
            node.impact
        );
        writeln!(
            &mut s,
            "  \"{}\" [label=\"{}\", fillcolor=\"{}\"];",
            dot_escape(&node.name),
            label,
            color
        )
        .expect("invariant: write to String");
    }
    // Emit edges. De-dup across sorted output.
    for node in &nodes {
        for succ in &node.direct_deps {
            if graph.nodes.contains_key(succ) {
                writeln!(
                    &mut s,
                    "  \"{}\" -> \"{}\";",
                    dot_escape(&node.name),
                    dot_escape(succ)
                )
                .expect("invariant: write to String");
            }
        }
    }
    writeln!(&mut s, "}}").expect("invariant: write to String");
    s
}

/// Render an `--unblock` ranked list as plain ASCII text.
///
/// Columns: `rank  impact  direct  class  name`. Header + a divider.
#[must_use]
pub fn emit_unblock_text(root: &str, ranked: &[UnblockCandidate]) -> String {
    // `writeln!` to `String` is infallible.
    let mut s = String::new();
    writeln!(
        &mut s,
        "# Unblock ranking for headline: {root}\n\
         # Higher impact = more closure nodes unblocked by promoting this entry.\n\
         # Class legend: DomainAxiom, TrustMarker, Unchecked.\n"
    )
    .expect("invariant: write to String");
    writeln!(
        &mut s,
        "{:>4}  {:>6}  {:>6}  {:<18}  name",
        "rank", "impact", "direct", "class"
    )
    .expect("invariant: write to String");
    writeln!(
        &mut s,
        "{:->4}  {:->6}  {:->6}  {:-<18}  {:-<60}",
        "", "", "", "", ""
    )
    .expect("invariant: write to String");
    for (i, c) in ranked.iter().enumerate() {
        writeln!(
            &mut s,
            "{:>4}  {:>6}  {:>6}  {:<18}  {}",
            i + 1,
            c.impact,
            c.direct_dependents,
            class_label(c.class),
            c.name
        )
        .expect("invariant: write to String");
    }
    if ranked.is_empty() {
        writeln!(
            &mut s,
            "(no promotion targets — closure is already constructive)"
        )
        .expect("invariant: write to String");
    }
    s
}

/// Render an `--impact <lemma>` result as plain ASCII text.
///
/// Lines of the form `headline  impact  direct` sorted by impact desc.
#[must_use]
pub fn emit_impact_text(lemma: &str, per_headline: &[(String, usize, usize)]) -> String {
    // `writeln!` to `String` is infallible.
    let mut s = String::new();
    writeln!(
        &mut s,
        "# Impact of promoting `{lemma}` on each known headline.\n\
         # impact = closure-size-delta; direct = first-step dependents.\n"
    )
    .expect("invariant: write to String");
    writeln!(&mut s, "{:>6}  {:>6}  headline", "impact", "direct")
        .expect("invariant: write to String");
    writeln!(&mut s, "{:->6}  {:->6}  {:-<60}", "", "", "").expect("invariant: write to String");
    let mut sorted: Vec<&(String, usize, usize)> = per_headline.iter().collect();
    sorted.sort_by(|a, b| {
        b.1.cmp(&a.1)
            .then_with(|| b.2.cmp(&a.2))
            .then_with(|| a.0.cmp(&b.0))
    });
    for (headline, impact, direct) in sorted {
        writeln!(&mut s, "{:>6}  {:>6}  {}", impact, direct, headline)
            .expect("invariant: write to String");
    }
    if per_headline.is_empty() {
        writeln!(&mut s, "(lemma is not in any known headline closure)")
            .expect("invariant: write to String");
    }
    s
}

fn class_color(class: NodeClass) -> &'static str {
    match class {
        NodeClass::ConstructiveTheorem => "#cfe8cf",
        NodeClass::AxiomDependentTheorem => "#fff2b3",
        NodeClass::DomainAxiom => "#f4b6b6",
        NodeClass::FoundationalAxiom => "#e0e0e0",
        NodeClass::TrustMarker => "#d9b3ff",
        NodeClass::Definition => "#cce0ff",
        NodeClass::Unchecked | NodeClass::Missing => "#ffcc80",
    }
}

fn class_label(class: NodeClass) -> &'static str {
    match class {
        NodeClass::ConstructiveTheorem => "Constructive",
        NodeClass::AxiomDependentTheorem => "AxiomDependent",
        NodeClass::DomainAxiom => "DomainAxiom",
        NodeClass::FoundationalAxiom => "Foundational",
        NodeClass::TrustMarker => "TrustMarker",
        NodeClass::Definition => "Definition",
        NodeClass::Unchecked => "Unchecked",
        NodeClass::Missing => "Missing",
    }
}

/// Escape `"` and `\` for DOT string literals. Newlines are not expected
/// in kernel Name components.
fn dot_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::depgraph::analyze::{build_closure, rank_unblock_candidates};
    use crate::depgraph::seed::seed_environment;
    use clean_kernel::{Environment, Name};

    #[test]
    fn json_round_trips() {
        let mut env = Environment::new();
        seed_environment(&mut env);
        let root = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
        let graph = build_closure(&env, &root).unwrap();
        let json = emit_headline_json(&graph);
        // Round-trip via serde_json::Value so we don't need Deserialize.
        let v: serde_json::Value = serde_json::from_str(&json).expect("JSON parses");
        assert_eq!(
            v["root"].as_str().unwrap(),
            "NNVerify.C006.blockwise_equals_monolithic"
        );
        assert!(v["nodes"].is_object());
    }

    #[test]
    fn dot_starts_with_digraph() {
        let mut env = Environment::new();
        seed_environment(&mut env);
        let root = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
        let graph = build_closure(&env, &root).unwrap();
        let dot = emit_dot(&graph);
        assert!(dot.starts_with("digraph depgraph {"));
        assert!(dot.contains("NNVerify.C006.blockwise_equals_monolithic"));
    }

    #[test]
    fn unblock_text_has_header() {
        let mut env = Environment::new();
        seed_environment(&mut env);
        let root = Name::from_string("NNVerify.C006.blockwise_equals_monolithic");
        let graph = build_closure(&env, &root).unwrap();
        let ranked = rank_unblock_candidates(&graph, Some(3));
        let text = emit_unblock_text(&graph.root, &ranked);
        assert!(text.contains("# Unblock ranking"));
        assert!(text.contains("rank"));
    }
}
