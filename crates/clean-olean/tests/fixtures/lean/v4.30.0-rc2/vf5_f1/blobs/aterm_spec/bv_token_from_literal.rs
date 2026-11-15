#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-lz4/src/block/compress.rs `token_from_literal`
pub const fn token_from_literal(lit_len: usize) -> u8 {
    if lit_len < 0xF {
        (lit_len as u8) << 4
    } else {
        0xF0
    }
}
/// aterm-lz4 SPECS.md compress-short-input-is-literal-and-conformant (the
/// `token_from_literal` helper sub-clause): token_from_literal(l) = if l < 15 then
/// (l as u8) << 4 else 0xF0, spelled as the number 16·l below 15 (the literal nibble
/// holds `l`, the match nibble is 0), else 0xF0.
pub fn token_from_literal_spec(lit_len: usize) -> u8 {
    let result = if lit_len < 0xF {
        (lit_len as u8) << 4
    } else {
        0xF0
    };
    let ok = if lit_len < 15 {
        result as usize == lit_len * 16
    } else {
        result == 240
    };
    let z = ok as u8;
    z - 1 + 1
}
