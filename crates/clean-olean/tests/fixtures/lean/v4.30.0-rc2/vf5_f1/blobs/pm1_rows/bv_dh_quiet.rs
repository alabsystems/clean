#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/devtools_helper.rs `quiet`
/// Whether now is a moment to put System Settings in front of the owner unasked: an aterm window
/// is focused, the owner is present ([`PRESENT_WITHIN`]) but not typing or pointing
/// ([`QUIET_FOR`]), this process has settled ([`Lane::settled`]), and no update hand-off is
/// pending or in flight.
#[must_use]
pub const fn quiet(
    focused: bool,
    input_within_quiet: bool,
    input_within_presence: bool,
    settled: bool,
    handoff_busy: bool,
) -> bool {
    focused && !input_within_quiet && input_within_presence && settled && !handoff_busy
}
/// aterm-gui SPECS.md dh-quiet (the quiet clause): quiet(focused, typing, present, settled, busy) = focused and not typing and present and settled and not busy. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn dh_quiet_spec(
    focused: bool,
    input_within_quiet: bool,
    input_within_presence: bool,
    settled: bool,
    handoff_busy: bool,
) -> u8 {
    let result =
        focused && !input_within_quiet && input_within_presence && settled && !handoff_busy;
    let ok = result
        == (focused as u8
            + !input_within_quiet as u8
            + input_within_presence as u8
            + settled as u8
            + !handoff_busy as u8
            == 5);
    let z = ok as u8;
    z - 1 + 1
}
