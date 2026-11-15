#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-png/src/decode.rs `mask_trns_key`
pub const fn mask_trns_key(key: u16, depth: u32) -> u16 {
    if depth < 16 {
        key & 0x00FF
    } else {
        key
    }
}
/// aterm-png SPECS.md decode-denotation (clause iv): a colour key at depth < 16 is masked
/// with 0x00FF: mask_trns_key(k, d) = if d < 16 then k & 0xFF else k, the mask spelled as
/// the remainder by 256.
pub fn mask_trns_key_spec(key: u16, depth: u32) -> u8 {
    let result = if depth < 16 { key & 0x00FF } else { key };
    let ok = if depth < 16 {
        result == key % 256
    } else {
        result == key
    };
    let z = ok as u8;
    z - 1 + 1
}
