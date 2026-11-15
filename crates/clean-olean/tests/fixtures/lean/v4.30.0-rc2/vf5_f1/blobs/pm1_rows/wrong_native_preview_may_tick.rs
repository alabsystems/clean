#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_native_preview_may_tick.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `native_preview_may_tick`'s clause without focus: false at (true, false, false, false).
pub fn native_preview_may_tick_wrong(
    has_os_window: bool,
    focused: bool,
    recorded: bool,
    overlay_open: bool,
) -> u8 {
    let result = (recorded || (has_os_window && focused)) && !overlay_open;
    let ok =
        result == ((has_os_window as u8 + recorded as u8 >= 1) as u8 + !overlay_open as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
