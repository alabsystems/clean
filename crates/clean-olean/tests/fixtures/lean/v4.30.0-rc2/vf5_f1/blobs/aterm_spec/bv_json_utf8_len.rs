#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-codec/src/json.rs `utf8_len`
pub const fn utf8_len(b: u8) -> usize {
    if b >= 0xf0 {
        4
    } else if b >= 0xe0 {
        3
    } else {
        2
    }
}
/// aterm-codec SPECS.md json-escape-reference (the `utf8_len` helper): the UTF-8 lead-byte
/// length, 4 for b >= 0xF0, 3 for b >= 0xE0, else 2, read on the high nibble (`b >> 4`).
pub fn utf8_len_spec(b: u8) -> u8 {
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
        result == 3
    } else {
        result == 2
    };
    let z = ok as u8;
    z - 1 + 1
}
