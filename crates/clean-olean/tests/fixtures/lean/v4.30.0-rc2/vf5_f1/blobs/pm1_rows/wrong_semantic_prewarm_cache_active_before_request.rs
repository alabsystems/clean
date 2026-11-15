#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_semantic_prewarm_cache_active_before_request.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `semantic_prewarm_cache_active_before_request`'s clause ignoring the match: false at (true, true, true).
pub fn semantic_prewarm_cache_active_before_request_wrong(
    active_present: bool,
    active_ready: bool,
    candidate_matches: bool,
) -> u8 {
    let result = active_present && active_ready && !candidate_matches;
    let ok = result == (active_present as u8 + active_ready as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
