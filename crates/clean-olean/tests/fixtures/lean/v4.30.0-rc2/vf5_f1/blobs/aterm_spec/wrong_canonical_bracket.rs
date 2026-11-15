#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_canonical_bracket.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `canonical_bracket`'s clause mapping 0x232A to 0x3008: false at 0x232A.
pub fn canonical_bracket_wrong(u: u32) -> u8 {
    let result = if u == 0x2329 {
        0x3008
    } else if u == 0x232A {
        0x3009
    } else {
        u
    };
    let ok = (u == 0x2329 && result == 0x3008)
        || (u == 0x232A && result == 0x3008)
        || (u != 0x2329 && u != 0x232A && result == u);
    let z = ok as u8;
    z - 1 + 1
}
