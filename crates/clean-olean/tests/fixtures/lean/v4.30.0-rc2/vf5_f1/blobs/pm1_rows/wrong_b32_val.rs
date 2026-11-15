#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_b32_val.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `b32_val`'s clause forgetting that u is not in the alphabet: false at 'v'.
pub fn b32_val_wrong(c: u8) -> u8 {
    let result = if c >= b'0' && c <= b'9' {
        c - b'0'
    } else if c >= b'a' && c <= b'h' {
        c - b'a' + 10
    } else if c == b'j' || c == b'k' {
        c - b'j' + 18
    } else if c == b'm' || c == b'n' {
        c - b'm' + 20
    } else if c >= b'p' && c <= b't' {
        c - b'p' + 22
    } else if c >= b'v' && c <= b'z' {
        c - b'v' + 27
    } else {
        0
    };
    let digit = c >= 48 && c <= 57;
    let letter = c >= 97 && c <= 122 && c != 105 && c != 108 && c != 111 && c != 117;
    let ok = if digit {
        result as u32 + 48 == c as u32
    } else if letter {
        result as u32 + 87 + (c > 105) as u32 + (c > 108) as u32 + (c > 111) as u32 == c as u32
    } else {
        result == 0
    };
    let z = ok as u8;
    z - 1 + 1
}
