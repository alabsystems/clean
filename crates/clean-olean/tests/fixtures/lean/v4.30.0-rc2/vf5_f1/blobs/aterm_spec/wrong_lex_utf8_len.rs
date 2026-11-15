#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_lex_utf8_len.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `lex::utf8_len`'s clause reading the two-byte lead as `>> 6 == 2`: false at 0xC0.
pub fn lex_utf8_len_wrong(lead: u8) -> u8 {
    let result = match lead {
        0xF0..=0xFF => 4,
        0xE0..=0xEF => 3,
        0xC0..=0xDF => 2,
        _ => 1,
    };
    let ok = if lead >> 4 == 15 {
        result == 4
    } else if lead >> 4 == 14 {
        result == 3
    } else if lead >> 6 == 2 {
        result == 2
    } else {
        result == 1
    };
    let z = ok as u8;
    z - 1 + 1
}
