#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `semantic_prewarm_result_is_current`
/// Generation guard at the semantic-font worker's installation boundary.
pub const fn semantic_prewarm_result_is_current(
    current_generation: u64,
    result_generation: u64,
) -> bool {
    current_generation == result_generation
}
/// aterm-gui SPECS.md semantic-prewarm-guards-refine-models (the `result_is_current` closed
/// form): result_is_current(c, r) = (c == r), spelled as c <= r and r <= c.
pub fn semantic_prewarm_result_is_current_spec(
    current_generation: u64,
    result_generation: u64,
) -> u8 {
    let result = current_generation == result_generation;
    let ok = result
        == (current_generation <= result_generation && result_generation <= current_generation);
    let z = ok as u8;
    z - 1 + 1
}
