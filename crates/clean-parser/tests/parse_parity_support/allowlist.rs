// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Pinned currently-divergent probes for `parse_parity.rs`. `include!`d there;
// see that file's header for the ratchet rule and brick-tag glossary. Regenerate
// alongside the fixture (see tests/fixtures/parser_parity/README.md).
//
// After Brick 3 (operator/notation coverage) the residual divergences are the
// intentionally-retained ones:
//   * `B3-bigop-gate`     — `∑ ∏ ∑' ∏' ⋃ ⋂ ∑ ∈` are Mathlib-only (plain Lean
//                           rejects them). clean ACCEPTS them as a deliberate
//                           Mathlib-lane superset (`∑`→`tsum`, `⋃`→`Set.iUnion`,
//                           …); gating them off would break `grammar/tests.rs`
//                           and the olean-import lane, so the over-acceptance is
//                           pinned rather than removed.
//   * `B3-setbuilder-gate`— `{x | p}` set-builder is Mathlib-only; clean accepts
//                           it as `setOf` (a documented superset — the
//                           `no_silent_trees` controls rely on it parsing).
//   * `B3-setprod-gate`   — `×ˢ` is Mathlib's set/finset product notation;
//                           clean accepts it as `SProd.sprod` for the Mathlib
//                           compatibility lane while core Lean rejects it.
//   * `B3-existsunique-gate` — `∃!` is Mathlib-only; clean accepts it.
//   * `B3-patternfun-globalname` — `fun (some x) =>` needs global-name
//                           resolution to become a pattern; clean flattens it to
//                           ordinary binders (elaborator-side, out of parser
//                           scope).
//   * `B3-getelem-postfix-ws` — once `xs[i]` parses, `xs[1] !` / `xs[1] ?` are
//                           consumed by clean's general postfix `!` (get-or-panic)
//                           and `?` (synthetic-hole) leniency; Lean rejects the
//                           whitespace-separated forms at parse time. Pre-existing
//                           postfix behavior exposed by GetElem, orthogonal to it.
pub const ALLOWLIST: &[(&str, &str, &str)] = &[
    // Big-operator notation — Mathlib-only, accepted as a superset.
    ("bigop", "∑ i, i", "B3-bigop-gate"),
    ("bigop", "fun (f : Nat → Nat) => ∑ i, f i", "B3-bigop-gate"),
    ("bigop", "∏ i, (i : Nat)", "B3-bigop-gate"),
    ("bigop", "∑' i, (i : Nat)", "B3-bigop-gate"),
    ("bigop", "∏' i, (i : Nat)", "B3-bigop-gate"),
    ("bigop", "∑ i ∈ [1,2,3], i", "B3-bigop-gate"),
    ("bigop", "⋃ i, ({i} : List Nat)", "B3-bigop-gate"),
    ("bigop", "⋂ i, ({i} : List Nat)", "B3-bigop-gate"),
    ("bigop", "∑ i, f i + g i", "B3-bigop-gate"),
    ("bigop", "∑ i, f i * 2", "B3-bigop-gate"),
    ("bigop", "∑ i j, i * j", "B3-bigop-gate"),
    ("bigop", "∑ i, i + 1", "B3-bigop-gate"),
    ("bigop", "∑ i, i * 2", "B3-bigop-gate"),
    ("bigop", "⨆ i, (i : Nat)", "B3-bigop-gate"),
    ("bigop", "⨅ i, (i : Nat)", "B3-bigop-gate"),
    // Set-builder — Mathlib-only, accepted as `setOf` (superset).
    ("brace", "{ x | x > 3 }", "B3-setbuilder-gate"),
    ("brace", "{ x ∈ s | x > 1 }", "B3-setbuilder-gate"),
    ("freqsweep", "{n : Nat | n > 0}", "B3-setbuilder-gate"),
    ("freqsweep", "∑ i ∈ Finset.range 3, i", "B3-bigop-gate"),
    // Unique-existence — Mathlib-only, accepted (superset).
    ("binder", "∃! x : Nat, x = 1", "B3-existsunique-gate"),
    // Pattern-fun global-name resolution — elaborator-side, out of parser scope.
    (
        "binder",
        "(fun (some x) => x : Option Nat → Nat) (some 5)",
        "B3-patternfun-globalname",
    ),
    // GetElem postfix `!`/`?` whitespace leniency (pre-existing clean postfix
    // behavior exposed once `xs[i]` parses).
    ("getelem", "xs[1] !", "B3-getelem-postfix-ws"),
    ("getelem", "xs[1] ?", "B3-getelem-postfix-ws"),
    // Set/finset product — Mathlib-only, accepted as `SProd.sprod` (superset).
    ("rewrite", "(1, 2) ×ˢ 3", "B3-setprod-gate"),
    ("rewrite", "(a, b) ×ˢ s", "B3-setprod-gate"),
    ("rewrite", "a ×ˢ b ×ˢ c", "B3-setprod-gate"),
    ("rewrite", "[1, 2] ×ˢ [10, 20]", "B3-setprod-gate"),
    ("rewrite", "a ×ˢ b ^ c", "B3-setprod-gate"),
];
