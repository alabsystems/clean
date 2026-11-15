#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_colorref_swap.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `colorref_swap`'s clause as a full involution: false at c = 2^24.
pub fn colorref_swap_wrong(c: u32) -> u8 {
    let result = ((c & 0xFF) << 16) | (c & 0xFF00) | ((c >> 16) & 0xFF);
    let twice = ((result & 0xFF) << 16) | (result & 0xFF00) | ((result >> 16) & 0xFF);
    let ok = result <= 0xFF_FFFF && twice == c;
    let z = ok as u8;
    z - 1 + 1
}
