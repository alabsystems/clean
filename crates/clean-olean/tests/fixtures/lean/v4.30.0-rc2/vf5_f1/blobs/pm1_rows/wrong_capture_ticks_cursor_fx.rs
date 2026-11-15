#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_capture_ticks_cursor_fx.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `capture_ticks_cursor_fx`'s clause ignoring the window: false at (true, false).
pub fn capture_ticks_cursor_fx_wrong(has_os_window: bool, recording_this_window: bool) -> u8 {
    let result = !has_os_window && !recording_this_window;
    let ok = result == (recording_this_window as u8 == 0);
    let z = ok as u8;
    z - 1 + 1
}
