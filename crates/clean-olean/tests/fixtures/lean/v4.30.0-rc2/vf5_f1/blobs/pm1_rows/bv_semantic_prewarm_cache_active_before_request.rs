#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `semantic_prewarm_cache_active_before_request`
/// Whether scheduling an uncached semantic-font candidate must first move the active renderer into the candidate cache.
#[must_use]
pub const fn semantic_prewarm_cache_active_before_request(
    active_present: bool,
    active_ready: bool,
    candidate_matches: bool,
) -> bool {
    active_present && active_ready && !candidate_matches
}
/// aterm-gui SPECS.md semantic-prewarm-guards-refine-models (closed form): cache_active_before_request(p, ready, m) = p and ready and not m. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn semantic_prewarm_cache_active_before_request_spec(
    active_present: bool,
    active_ready: bool,
    candidate_matches: bool,
) -> u8 {
    let result = active_present && active_ready && !candidate_matches;
    let ok = result == (active_present as u8 + active_ready as u8 + !candidate_matches as u8 == 3);
    let z = ok as u8;
    z - 1 + 1
}
