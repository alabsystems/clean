// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Expansion golden lock** — real corpus props aligned to the exact Lean
//! statement the expanded fragment library must produce.
//!
//! Unlike [`super::golden_tests`] (batch-3 hand translations, order-insensitive),
//! this fixture pins the **byte-exact** (whitespace-collapsed) rendering of the
//! Path-B harness-expansion mappings (`∈`/`⊆`/`⊂`/`∣`/`<+:`/`<:+`/`Set.image`/
//! `Set.InjOn`/`Set.BijOn`/`insert`/`.Finite`/`.Nodup`/`List.zip`/`::`/`max`/
//! `min`/`.toNat`/`True`/`False`) plus, from the **binder round**, the six
//! quantifier / comprehension shapes (`∀ x, …`/`∃ x, …`/`∃! x, …`/`∀ x ∈ S, …`/
//! `∃ x ∈ S, …`/`{x | …}`, including nested and concrete-typed binders and the
//! capture-safe de Bruijn opening) plus, from **coverage-round 3**, the nine
//! post-binder shapes (`List.list.set` → `{x | x ∈ xs}`, `List.sorted_wrt` →
//! `List.Pairwise`, `bot`/`top` on `Set` → `∅`/`Set.univ`, `Sup`/`Inf` on a set
//! of sets → `sSup`/`sInf`, `Finite_Set.card` → `.ncard`, `gcd`/`lcm` on `ℕ` →
//! `Nat.gcd`/`Nat.lcm`). Each `lean_statement` was hand-verified as a faithful
//! transcription of its Isabelle `prop` (the spot-check gate), so any drift in a
//! renderer — a flipped argument, a wrong Mathlib name, a mis-opened binder —
//! fails here loudly. The props are the actual main_v3 corpus statements
//! (serials recorded).

use super::super::isabelle_pure::IsaTerm;
use super::translate_prop;
use super::types::LeanGoal;

const GOLDEN: &str = include_str!("../../../tests/fixtures/isabelle/pathb_expansion_golden.jsonl");

struct Pair {
    id: String,
    lean: String,
    prop: IsaTerm,
    want: String,
}

fn load() -> Vec<Pair> {
    GOLDEN
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: serde_json::Value = serde_json::from_str(l).expect("golden line is JSON");
            Pair {
                id: v["id"].as_str().expect("id").to_string(),
                lean: v["lean"].as_str().expect("lean").to_string(),
                prop: serde_json::from_value(v["prop"].clone()).expect("prop is an IsaTerm"),
                want: v["lean_statement"].as_str().expect("stmt").to_string(),
            }
        })
        .collect()
}

/// Collapse all whitespace runs to a single space and trim.
fn collapse_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn expansion_golden_reproduces_faithful_statements_exactly() {
    let pairs = load();
    assert_eq!(
        pairs.len(),
        55,
        "expected 55 expansion golden pairs (28 fragment-expansion + 12 binder + 15 round-3)"
    );
    let mut failures = Vec::new();
    for p in &pairs {
        match translate_prop(&p.prop, &p.lean) {
            LeanGoal::Supported(sg) => {
                if collapse_ws(&sg.signature) != collapse_ws(&p.want) {
                    failures.push(format!(
                        "{} ({}):\n  want: {}\n  got:  {}",
                        p.id,
                        p.lean,
                        collapse_ws(&p.want),
                        collapse_ws(&sg.signature)
                    ));
                }
            }
            LeanGoal::Unsupported(u) => {
                failures.push(format!(
                    "{} ({}): regressed to Unsupported({u})",
                    p.id, p.lean
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "FAITHFULNESS/RENDER DRIFT in the expansion mappings:\n{}",
        failures.join("\n")
    );
}
