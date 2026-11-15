#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_is_word.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `is_word`'s clause without `_` (the gaps 91..=94 and 96 one gap 91..=96): false at 0x5F.
pub fn is_word_wrong(b: u8) -> u8 {
    let result = (b >= b'0' && b <= b'9')
        || (b >= b'A' && b <= b'Z')
        || (b >= b'a' && b <= b'z')
        || b == b'_';
    let gap = b < 48 || (57 < b && b < 65) || (90 < b && b < 97) || 122 < b;
    let ok = result == !gap;
    let z = ok as u8;
    z - 1 + 1
}
