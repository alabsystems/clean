#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/metrics.rs `tainted_at`
pub const fn tainted_at(
    capture_forced: bool,
    now_ns: u64,
    taint_until_ns: u64,
    capture_depth: u64,
) -> bool {
    capture_forced || capture_depth != 0 || now_ns < taint_until_ns
}
/// aterm-gui SPECS.md m-tainted-at (the tainted_at clause): tainted_at(forced, now, until, depth) = forced || depth != 0 || now < until. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn tainted_at_spec(
    capture_forced: bool,
    now_ns: u64,
    taint_until_ns: u64,
    capture_depth: u64,
) -> u8 {
    let result = capture_forced || capture_depth != 0 || now_ns < taint_until_ns;
    let ok = result
        == (capture_forced as u8 + (capture_depth > 0) as u8 + (taint_until_ns > now_ns) as u8
            >= 1);
    let z = ok as u8;
    z - 1 + 1
}
