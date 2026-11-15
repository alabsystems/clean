#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_token_from_literal.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `token_from_literal`'s clause as 8·l: false at 1.
pub fn token_from_literal_wrong(lit_len: usize) -> u8 {
    let result = if lit_len < 0xF {
        (lit_len as u8) << 4
    } else {
        0xF0
    };
    let ok = if lit_len < 15 {
        result as usize == lit_len * 8
    } else {
        result == 240
    };
    let z = ok as u8;
    z - 1 + 1
}
