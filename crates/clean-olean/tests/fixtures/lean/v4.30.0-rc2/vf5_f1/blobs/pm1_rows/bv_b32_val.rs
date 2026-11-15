#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/atpkg-keys/src/master.rs `b32_val`
pub const fn b32_val(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'h' => c - b'a' + 10,
        b'j' | b'k' => c - b'j' + 18,
        b'm' | b'n' => c - b'm' + 20,
        b'p'..=b't' => c - b'p' + 22,
        b'v'..=b'z' => c - b'v' + 27,
        _ => 0,
    }
}
/// atpkg-keys SPECS.md master-seed-decode (the `b32_val` half): for c in ALPHABET =
/// "0123456789abcdefghjkmnpqrstvwxyz", b32_val(c) is c's index there, else 0. Spelled apart
/// from the arms: a digit's index is c - 48; a lowercase letter other than i, l, o, u has
/// index c - 87 less the number of those four below it. The harness's copy writes the
/// `match` as the `if` chain it is (the same function on every `u8`): F1's `switch` keeps no
/// `c != x` on its default arm.
pub fn b32_val_spec(c: u8) -> u8 {
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
        result as u32
            + 87
            + (c > 105) as u32
            + (c > 108) as u32
            + (c > 111) as u32
            + (c > 117) as u32
            == c as u32
    } else {
        result == 0
    };
    let z = ok as u8;
    z - 1 + 1
}
