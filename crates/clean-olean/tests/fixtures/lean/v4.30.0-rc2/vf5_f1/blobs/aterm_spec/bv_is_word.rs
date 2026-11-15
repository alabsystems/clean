#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-census/src/guards/mod.rs `is_word`, REWRITTEN for F1 (aterm's body
// calls `is_ascii_alphanumeric`, which trust-ir lowers to a call): `b.is_ascii_alphanumeric()`
// is `matches!(b, b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z')`, core's own definition (the
// plan's measured fix), and the three ranges are written as comparisons, because the
// stage-2 compiler's THIR lowering refuses an or-pattern of ranges ("Match(or-pattern
// element unsupported)": the function is left out of the artifact). The same function on
// every `u8`.
//
//     pub(crate) const fn is_word(b: u8) -> bool {
//         b.is_ascii_alphanumeric() || b == b'_'
//     }
pub const fn is_word(b: u8) -> bool {
    (b >= b'0' && b <= b'9') || (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z') || b == b'_'
}
/// aterm-census SPECS.md census-guard-calls (the scalar half): is_word(b) iff b is in
/// [0-9A-Za-z_], spelled as the complement: b is in none of the gaps below 48, 58..=64,
/// 91..=94, 96 and above 122.
pub fn is_word_spec(b: u8) -> u8 {
    let result = (b >= b'0' && b <= b'9')
        || (b >= b'A' && b <= b'Z')
        || (b >= b'a' && b <= b'z')
        || b == b'_';
    let gap = b < 48 || (57 < b && b < 65) || (90 < b && b < 95) || (95 < b && b < 97) || 122 < b;
    let ok = result == !gap;
    let z = ok as u8;
    z - 1 + 1
}
