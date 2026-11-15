#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-render/src/ligature_shaping.rs `shaping_min_run`
pub const fn shaping_min_run(has_user_features: bool) -> usize {
    if has_user_features {
        1
    } else {
        2
    }
}
/// aterm-render SPECS.md shaping-gate (the `shaping_min_run` half): shaping_min_run(u) =
/// if u {1} else {2}.
pub fn shaping_min_run_spec(has_user_features: bool) -> u8 {
    let result = if has_user_features { 1 } else { 2 };
    let ok = (has_user_features && result == 1) || (!has_user_features && result == 2);
    let z = ok as u8;
    z - 1 + 1
}
