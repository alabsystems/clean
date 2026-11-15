#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_ink_skip_applies_to_width.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `ink_skip_applies_to_width`'s clause as cols = 0: false at 1.
pub fn ink_skip_applies_to_width_wrong(cols: usize) -> u8 {
    let result = cols <= 1;
    let ok = result == (cols == 0);
    let z = ok as u8;
    z - 1 + 1
}
