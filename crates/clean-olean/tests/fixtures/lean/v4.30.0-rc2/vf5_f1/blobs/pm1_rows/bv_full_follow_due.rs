#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/harness_host.rs `full_follow_due`
/// A generic wake always owes a full follow.
pub const fn full_follow_due(
    timed_out: bool,
    full_before: u64,
    full_now: u64,
    phase_before: u64,
    phase_now: u64,
) -> bool {
    timed_out || full_before != full_now || phase_now < phase_before || phase_now - phase_before > 1
}
/// aterm-gui SPECS.md hh-full-follow-due (the first clause): full_follow_due(t, fb, fn, pb,
/// pn) = t or fb != fn or pn < pb or pn - pb > 1, spelled as a count with the phase step
/// read as "pn is neither pb nor pb + 1".
pub fn full_follow_due_spec(
    timed_out: bool,
    full_before: u64,
    full_now: u64,
    phase_before: u64,
    phase_now: u64,
) -> u8 {
    let result = timed_out
        || full_before != full_now
        || phase_now < phase_before
        || phase_now - phase_before > 1;
    let jump = if phase_now == phase_before {
        false
    } else {
        !(phase_before < u64::MAX && phase_now == phase_before + 1)
    };
    let ok = result == (timed_out as u8 + (full_before != full_now) as u8 + jump as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
