#![allow(dead_code)]
// A VF7 negative control (Clean docs/DECISIONS.md R206): the harness of `bv_level_bit.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

/// `level_bit`'s clause with the power-of-two branch reaching `depth < 33`: false at 32.
pub fn level_bit_wrong(depth: u16) -> u8 {
    let result = if depth < 32 { 1u32 << depth } else { 0 };
    let ok = if depth < 33 {
        result != 0 && result & (result - 1) == 0 && result >> depth == 1
    } else {
        result == 0
    };
    let z = ok as u8;
    z - 1 + 1
}
