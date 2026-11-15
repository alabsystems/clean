#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `defer_gpu_build`
pub const fn defer_gpu_build(want_gpu: bool, headless: bool) -> bool {
    want_gpu && headless
}
/// aterm-gui SPECS.md defer-gpu-build: for all g, h: defer_gpu_build(g, h) = g and h. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn defer_gpu_build_spec(want_gpu: bool, headless: bool) -> u8 {
    let result = want_gpu && headless;
    let ok = result == (want_gpu as u8 + headless as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
