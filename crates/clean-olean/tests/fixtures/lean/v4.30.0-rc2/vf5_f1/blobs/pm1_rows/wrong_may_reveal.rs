#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_may_reveal.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `may_reveal`'s clause ignoring a drag: false at (true, false, true).
pub fn may_reveal_wrong(settings_front: bool, visible: bool, dragging: bool) -> u8 {
    let result = settings_front && !visible && !dragging;
    let ok = result == (settings_front as u8 + !visible as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
