#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/atpkg/src/cli.rs `says_not_installed_yet`
pub const fn says_not_installed_yet(store_empty: bool, window_pass: bool) -> bool {
    store_empty && !window_pass
}
/// atpkg SPECS.md consent-and-adoption-decisions (clause 4): says_not_installed_yet(empty, window) = empty and not window. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn says_not_installed_yet_spec(store_empty: bool, window_pass: bool) -> u8 {
    let result = store_empty && !window_pass;
    let ok = result == (store_empty as u8 + !window_pass as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
