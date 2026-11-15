#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_update_bar_press_applies.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `update_bar_press_applies`'s clause ignoring the hand-off: false at (true, true, false).
pub fn update_bar_press_applies_wrong(
    bar_is_staged: bool,
    staged_ready: bool,
    handoff_available: bool,
) -> u8 {
    let result = bar_is_staged && staged_ready && handoff_available;
    let ok = result == (bar_is_staged as u8 + staged_ready as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
