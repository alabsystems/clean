#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_boot_health_dispatch_windowed_fresh.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `should_dispatch_boot_health_confirmation`'s clause not asking a windowed launch for its OS window: false at (false, false, true, false, true, false, false).
pub fn boot_health_dispatch_windowed_fresh_wrong(
    headless: bool,
    headless_ready: bool,
    first_present_done: bool,
    already_dispatched: bool,
    retry_due: bool,
    has_os_window: bool,
    incoming_handoff_pending: bool,
) -> u8 {
    if !(!headless && !already_dispatched) {
        return 1;
    }
    let checkpoint = if headless {
        headless_ready
    } else {
        first_present_done && has_os_window
    };
    let result = checkpoint && !already_dispatched && retry_due && !incoming_handoff_pending;
    let reached = headless as u8 + headless_ready as u8 == 2
        || !headless as u8 + first_present_done as u8 == 2;
    let ok = result
        == (reached as u8
            + !already_dispatched as u8
            + retry_due as u8
            + !incoming_handoff_pending as u8
            == 4);
    let z = ok as u8;
    z - 1 + 1
}
