#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-census/src/lex.rs `utf8_len`
pub const fn utf8_len(lead: u8) -> usize {
    match lead {
        0xF0..=0xFF => 4,
        0xE0..=0xEF => 3,
        0xC0..=0xDF => 2,
        _ => 1,
    }
}
/// aterm-census SPECS.md census-lex-spans-refine (the `utf8_len` helper): F0..FF to 4,
/// E0..EF to 3, C0..DF to 2, else 1, read on the lead byte's high bits.
pub fn utf8_len_spec(lead: u8) -> u8 {
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
    } else if lead >> 6 == 3 {
        result == 2
    } else {
        result == 1
    };
    let z = ok as u8;
    z - 1 + 1
}
