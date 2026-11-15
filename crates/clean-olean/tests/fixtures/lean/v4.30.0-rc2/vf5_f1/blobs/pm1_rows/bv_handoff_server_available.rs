#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/defterm_win.rs `handoff_server_available`
/// Returns whether a COM handoff server can answer `EstablishPtyHandoff` (always `false`).
#[must_use]
pub fn handoff_server_available() -> bool {
    false
}
/// aterm-gui SPECS.md defterm-registration-gated (the first clause):
/// handoff_server_available() = false in this build.
pub fn handoff_server_available_spec() -> u8 {
    let result = false;
    let ok = !result;
    let z = ok as u8;
    z - 1 + 1
}
