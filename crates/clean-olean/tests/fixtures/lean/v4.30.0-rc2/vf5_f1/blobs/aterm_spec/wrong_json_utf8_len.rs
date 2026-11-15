#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_json_utf8_len.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `json::utf8_len`'s clause with 2 for the E nibble: false at 0xE0.
pub fn json_utf8_len_wrong(b: u8) -> u8 {
    let result = if b >= 0xf0 {
        4
    } else if b >= 0xe0 {
        3
    } else {
        2
    };
    let hi = b >> 4;
    let ok = if hi == 15 {
        result == 4
    } else if hi == 14 {
        result == 2
    } else {
        result == 2
    };
    let z = ok as u8;
    z - 1 + 1
}
