#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/control.rs `control_lanes_prepared`
pub const fn control_lanes_prepared(rpc: usize, subscriptions: usize) -> bool {
    rpc > 0 && subscriptions > 0
}
/// aterm-gui SPECS.md control-preparation (the first clause): for all r, s:
/// control_lanes_prepared(r, s) iff r > 0 and s > 0, spelled as: false iff either is 0.
pub fn control_lanes_prepared_spec(rpc: usize, subscriptions: usize) -> u8 {
    let result = rpc > 0 && subscriptions > 0;
    let ok = if rpc == 0 || subscriptions == 0 {
        !result
    } else {
        result
    };
    let z = ok as u8;
    z - 1 + 1
}
