// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Golden validation** against the hand-translated batch-3 pairs.
//!
//! The fixture `pathb_golden.jsonl` carries the 30 aligned
//! `(Isabelle prop JSON, Lean statement)` pairs extracted from batch-3's merged
//! artifacts (manifest + `notes/seeds.jsonl` props + `combined_verify.lean`
//! statements). Each pair drives the harness; the outcome is one of:
//!
//! * **Exact** — the harness reproduces the hand statement modulo whitespace and
//!   binder order/grouping/alpha (see [`normalize_sig`]);
//! * **Unsupported** — the harness declined (a first-class, honest miss);
//! * **Mismatch** — the harness emitted a *different* Supported statement. This
//!   is the only forbidden outcome (it would mean an unfaithful translation) and
//!   the test fails loudly on any.
//!
//! Coverage is reported and pinned per-id so the faithfulness contract is
//! regression-locked, not merely a floating percentage.

use std::collections::BTreeMap;

use super::super::isabelle_pure::IsaTerm;
use super::translate_prop;
use super::types::LeanGoal;

const GOLDEN: &str = include_str!("../../../tests/fixtures/isabelle/pathb_golden.jsonl");

/// The batch-3 ids the harness is expected to reproduce exactly.
const EXPECTED_EXACT: &[&str] = &[
    "c01", "c02", "c03", "c04", "c05", "c06", "c07", "c08", "c09", "c10", "c11", "c12", "c13",
    "c14", "c15", "c16", "c17", "c18", "c19", "c25", "c26", "c27", "c28",
];

/// The batch-3 ids that are honestly declined (class/locale premise, polymorphic
/// order, multiset, list-set embedding) — outside the faithful pattern library.
const EXPECTED_UNSUPPORTED: &[&str] = &["c20", "c21", "c22", "c23", "c24", "c29", "c30"];

#[derive(Debug)]
struct GoldenPair {
    id: String,
    lean: String,
    prop: IsaTerm,
    hand: String,
}

fn load_pairs() -> Vec<GoldenPair> {
    GOLDEN
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: serde_json::Value = serde_json::from_str(l).expect("golden line is JSON");
            let prop: IsaTerm =
                serde_json::from_value(v["prop"].clone()).expect("prop is an IsaTerm");
            GoldenPair {
                id: v["id"].as_str().expect("id").to_string(),
                lean: v["lean"].as_str().expect("lean").to_string(),
                prop,
                hand: v["lean_statement"].as_str().expect("stmt").to_string(),
            }
        })
        .collect()
}

/// Collapse all whitespace runs to a single space and trim.
fn collapse_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The bracket-depth-0 `:` that separates the binder region from the body.
fn depth0_colon(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => depth -= 1,
            ':' if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// The greek type-variable letters both the harness and the batch use.
const GREEKS: &[char] = &['α', 'β', 'γ', 'δ', 'ε', 'ζ', 'η', 'θ', 'ι', 'κ'];

/// One parsed binder: bracket kind, one variable name, and its type (`None` for
/// an instance binder `[…]`).
struct Binder {
    open: char,
    close: char,
    name: String,
    ty: Option<String>,
}

/// Parse a binder region into ordered, per-variable binders (`(a b : T)`
/// expands to one binder per name; `[Inst]` is a nameless instance binder).
fn parse_binders_ordered(region: &str) -> Vec<Binder> {
    let mut out = Vec::new();
    let chars: Vec<char> = region.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let open = chars[i];
        let close = match open {
            '(' => ')',
            '{' => '}',
            '[' => ']',
            _ => {
                i += 1;
                continue;
            }
        };
        let mut depth = 0i32;
        let start = i;
        while i < chars.len() {
            match chars[i] {
                '(' | '{' | '[' => depth += 1,
                ')' | '}' | ']' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        let inner: String = chars[start + 1..i].iter().collect();
        i += 1; // past close
        if open == '[' {
            out.push(Binder {
                open,
                close,
                name: inner.trim().to_string(),
                ty: None,
            });
            continue;
        }
        if let Some((names, ty)) = inner.split_once(':') {
            let ty = ty.trim().to_string();
            for name in names.split_whitespace() {
                out.push(Binder {
                    open,
                    close,
                    name: name.to_string(),
                    ty: Some(ty.clone()),
                });
            }
        } else {
            out.push(Binder {
                open,
                close,
                name: inner.trim().to_string(),
                ty: None,
            });
        }
    }
    out
}

/// Assign canonical names (`T0`, `T1`, …) to greek type variables in first-sight
/// order as `s` is scanned left to right, extending `map`.
fn scan_tvars(s: &str, map: &mut BTreeMap<char, String>) {
    for c in s.chars() {
        if GREEKS.contains(&c) && !map.contains_key(&c) {
            let id = map.len();
            map.insert(c, format!("T{id}"));
        }
    }
}

/// Replace every greek type-variable char with its canonical name.
fn apply_tvars(s: &str, map: &BTreeMap<char, String>) -> String {
    s.chars()
        .map(|c| map.get(&c).cloned().unwrap_or_else(|| c.to_string()))
        .collect()
}

/// Split a signature into a canonical `(binder_set, body)` pair, insensitive to
/// whitespace, binder order/grouping, **and type-variable renaming (alpha)**.
///
/// Type variables are canonicalized by first appearance while scanning the
/// binder types in a body-driven order: the hand and harness statements share
/// the term-variable names and the body, so the resulting `T0/T1/…` map is
/// identical whenever the two differ only by a consistent renaming of `α/β/γ`.
fn normalize_sig(sig: &str) -> (Vec<String>, String) {
    let sig = collapse_ws(sig);
    let colon = depth0_colon(&sig).expect("signature has a body colon");
    let (header, body) = sig.split_at(colon);
    let body = body[1..].trim().to_string();

    let region = header
        .trim()
        .strip_prefix("theorem")
        .map(str::trim)
        .and_then(|h| h.split_once(char::is_whitespace).map(|(_, rest)| rest))
        .unwrap_or("")
        .trim()
        .to_string();

    let binders = parse_binders_ordered(&region);

    let mut order: Vec<usize> = (0..binders.len()).collect();
    order.sort_by_key(|&i| (body.find(&binders[i].name).unwrap_or(usize::MAX), i));
    let mut map: BTreeMap<char, String> = BTreeMap::new();
    for &i in &order {
        if let Some(ty) = &binders[i].ty {
            scan_tvars(ty, &mut map);
        }
    }
    scan_tvars(&body, &mut map);

    let mut tokens: Vec<String> = binders
        .iter()
        .map(|b| {
            let name = apply_tvars(&b.name, &map);
            match &b.ty {
                Some(t) => format!("{}{} : {}{}", b.open, name, apply_tvars(t, &map), b.close),
                None => format!("{}{}{}", b.open, name, b.close),
            }
        })
        .collect();
    tokens.sort();
    (tokens, apply_tvars(&body, &map))
}

fn sigs_equivalent(a: &str, b: &str) -> bool {
    normalize_sig(a) == normalize_sig(b)
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Exact,
    Unsupported(String),
    Mismatch(String),
}

fn classify(pair: &GoldenPair) -> Outcome {
    match translate_prop(&pair.prop, &pair.lean) {
        LeanGoal::Unsupported(u) => Outcome::Unsupported(u.to_string()),
        LeanGoal::Supported(sg) => {
            if sigs_equivalent(&sg.signature, &pair.hand) {
                Outcome::Exact
            } else {
                Outcome::Mismatch(sg.signature)
            }
        }
    }
}

#[test]
fn golden_normalizer_is_order_and_grouping_insensitive() {
    let a = "theorem t {α : Type*} (xs ys : List α) :\n    xs = ys";
    let b = "theorem t (ys xs : List α) {α : Type*} :  xs   =  ys";
    assert!(
        sigs_equivalent(a, b),
        "binder order/grouping must not matter"
    );
    let c = "theorem t (xs : List α) (ys : List β) :\n    xs = ys";
    assert!(!sigs_equivalent(a, c), "binder types must matter");
    // Alpha: a consistent renaming of the bound type variables is equivalent.
    let d = "theorem t {α β : Type*} (f : α → β) (xs : List α) :\n    xs.map f = xs.map f";
    let e = "theorem t {α β : Type*} (f : β → α) (xs : List β) :\n    xs.map f = xs.map f";
    assert!(
        sigs_equivalent(d, e),
        "type-variable renaming must not matter"
    );
}

#[test]
fn golden_no_unfaithful_mismatch() {
    let pairs = load_pairs();
    assert_eq!(pairs.len(), 30, "expected 30 golden pairs");
    let mismatches: Vec<String> = pairs
        .iter()
        .filter_map(|p| match classify(p) {
            Outcome::Mismatch(got) => Some(format!("{} ({}): got `{}`", p.id, p.lean, got)),
            _ => None,
        })
        .collect();
    assert!(
        mismatches.is_empty(),
        "FAITHFULNESS VIOLATION — harness emitted a statement differing from the hand \
         translation (must be Exact or Unsupported):\n{}",
        mismatches.join("\n")
    );
}

#[test]
fn golden_coverage_matches_pinned_contract() {
    let pairs = load_pairs();
    let mut exact = Vec::new();
    let mut unsupported = Vec::new();
    for p in &pairs {
        match classify(p) {
            Outcome::Exact => exact.push(p.id.clone()),
            Outcome::Unsupported(_) => unsupported.push(p.id.clone()),
            Outcome::Mismatch(got) => panic!("{} mismatch: {got}", p.id),
        }
    }
    exact.sort();
    unsupported.sort();

    let mut want_exact: Vec<String> = EXPECTED_EXACT.iter().map(|s| s.to_string()).collect();
    want_exact.sort();
    let mut want_unsup: Vec<String> = EXPECTED_UNSUPPORTED.iter().map(|s| s.to_string()).collect();
    want_unsup.sort();

    assert_eq!(exact, want_exact, "the exactly-reproduced id set drifted");
    assert_eq!(unsupported, want_unsup, "the unsupported id set drifted");

    let coverage = 100.0 * exact.len() as f64 / pairs.len() as f64;
    // Honest, pinned coverage: 23/30 = 76.7%. Assert a stable floor and ceiling.
    assert!(
        (76.0..=77.0).contains(&coverage),
        "coverage {coverage:.1}% ({}/{}) drifted from the pinned 76.7%",
        exact.len(),
        pairs.len()
    );
    eprintln!(
        "PATH-B GOLDEN COVERAGE: {}/{} = {:.1}% exact; {} unsupported (curation tail)",
        exact.len(),
        pairs.len(),
        coverage,
        unsupported.len()
    );
}
