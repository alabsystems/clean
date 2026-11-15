#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `video_post_present_should_finalize`
pub const fn video_post_present_should_finalize(
    deadline_reached: bool,
    resized_or_format_stopped: bool,
) -> bool {
    deadline_reached || resized_or_format_stopped
}
/// aterm-gui SPECS.md capture-guards (the should_finalize clause): should_finalize(a, b) = a or b. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn video_post_present_should_finalize_spec(
    deadline_reached: bool,
    resized_or_format_stopped: bool,
) -> u8 {
    let result = deadline_reached || resized_or_format_stopped;
    let ok = result == (deadline_reached as u8 + resized_or_format_stopped as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
