#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_padding_for.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const BLOCK: usize = 512;

/// `padding_for`'s clause without the outer mod: false at 0.
pub fn padding_for_wrong(size: u64) -> u8 {
    let rem = size % BLOCK as u64;
    let result = if rem == 0 { 0 } else { BLOCK as u64 - rem };
    let ok = result == 512 - size % 512;
    let z = ok as u8;
    z - 1 + 1
}
