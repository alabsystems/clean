#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "PM-1-free, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `7543390498`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others).

// aterm: crates/aterm-bidi/src/lib.rs `canonical_bracket`
pub const fn canonical_bracket(u: u32) -> u32 {
    match u {
        0x2329 => 0x3008,
        0x232A => 0x3009,
        other => other,
    }
}
/// aterm-bidi SPECS.md bracket-of-table (the `canon` clause): canon maps 0x2329 to 0x3008
/// and 0x232A to 0x3009, and fixes everything else. The harness's copy writes the `match`
/// on two literals with a binding default as the `if`/`else if` chain it is (the same
/// function on every `u32`): F1's `switch` keeps no `u ≠ cᵢ` on its default arm, so the
/// match's own default path is the identity on a `u` the calculus cannot tell from 0x2329.
pub fn canonical_bracket_spec(u: u32) -> u8 {
    let result = if u == 0x2329 {
        0x3008
    } else if u == 0x232A {
        0x3009
    } else {
        u
    };
    let ok = (u == 0x2329 && result == 0x3008)
        || (u == 0x232A && result == 0x3009)
        || (u != 0x2329 && u != 0x232A && result == u);
    let z = ok as u8;
    z - 1 + 1
}
