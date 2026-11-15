#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/app_update_screen.rs `App::update_bar_press_applies`
/// Whether pressing the update row applies the staged build in place (requires
/// `FlowPhase::Staged`, `staged_ready`, and `handoff_available`).
pub const fn update_bar_press_applies(
    bar_is_staged: bool,
    staged_ready: bool,
    handoff_available: bool,
) -> bool {
    bar_is_staged && staged_ready && handoff_available
}
/// aterm-gui SPECS.md update-bar-press-and-route (first clause): update_bar_press_applies(staged, ready, handoff) = staged and ready and handoff. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn update_bar_press_applies_spec(
    bar_is_staged: bool,
    staged_ready: bool,
    handoff_available: bool,
) -> u8 {
    let result = bar_is_staged && staged_ready && handoff_available;
    let ok = result == (bar_is_staged as u8 + staged_ready as u8 + handoff_available as u8 == 3);
    let z = ok as u8;
    z - 1 + 1
}
