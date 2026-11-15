#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/lib.rs `should_dispatch_boot_health_confirmation`
#[must_use]
pub const fn should_dispatch_boot_health_confirmation(
    headless: bool,
    headless_ready: bool,
    first_present_done: bool,
    already_dispatched: bool,
    retry_due: bool,
    has_os_window: bool,
    incoming_handoff_pending: bool,
) -> bool {
    let checkpoint = if headless {
        headless_ready
    } else {
        first_present_done && has_os_window
    };
    checkpoint && !already_dispatched && retry_due && !incoming_handoff_pending
}
/// aterm-gui SPECS.md boot-health-dispatch (the first clause): should_dispatch(h, hr, fp,
/// d, due, os, hp) = (h ? hr : fp and os) and not d and due and not hp. Spelled as counts:
/// the checkpoint is (h, hr) both or (not h, fp, os) all three.
///
/// This harness is one of 4 parts of the row (the whole one is past the reference
/// entry's heartbeat budget): windowed, already dispatched; together the parts are the clause.
pub fn boot_health_dispatch_windowed_dispatched_spec(
    headless: bool,
    headless_ready: bool,
    first_present_done: bool,
    already_dispatched: bool,
    retry_due: bool,
    has_os_window: bool,
    incoming_handoff_pending: bool,
) -> u8 {
    if !(!headless && already_dispatched) {
        return 1;
    }
    let checkpoint = if headless {
        headless_ready
    } else {
        first_present_done && has_os_window
    };
    let result = checkpoint && !already_dispatched && retry_due && !incoming_handoff_pending;
    let reached = headless as u8 + headless_ready as u8 == 2
        || !headless as u8 + first_present_done as u8 + has_os_window as u8 == 3;
    let ok = result
        == (reached as u8
            + !already_dispatched as u8
            + retry_due as u8
            + !incoming_handoff_pending as u8
            == 4);
    let z = ok as u8;
    z - 1 + 1
}
