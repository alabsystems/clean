#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `semantic_prewarm_replacement_carries_base`
/// Whether the one-slot semantic-font queue still owns a committed renderer base after replacing a not-yet-started job.
#[must_use]
pub const fn semantic_prewarm_replacement_carries_base(
    new_has_base: bool,
    replaced_has_base: bool,
) -> bool {
    new_has_base || replaced_has_base
}
/// aterm-gui SPECS.md semantic-prewarm-guards-refine-models (closed form): replacement_carries_base(n, r) = n or r. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn semantic_prewarm_replacement_carries_base_spec(
    new_has_base: bool,
    replaced_has_base: bool,
) -> u8 {
    let result = new_has_base || replaced_has_base;
    let ok = result == (new_has_base as u8 + replaced_has_base as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
