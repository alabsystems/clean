#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/platform_win.rs `colorref_swap`
pub fn colorref_swap(c: u32) -> u32 {
    ((c & 0xFF) << 16) | (c & 0xFF00) | ((c >> 16) & 0xFF)
}
/// aterm-gui SPECS.md colorref-swap: colorref_swap(c) swaps the low and the third byte and
/// drops the top one, spelled with remainders and quotients by powers of 256; hence
/// colorref_swap(c) <= 0xFFFFFF and colorref_swap(colorref_swap(c)) = c mod 2^24 (the body
/// run twice).
pub fn colorref_swap_spec(c: u32) -> u8 {
    let result = ((c & 0xFF) << 16) | (c & 0xFF00) | ((c >> 16) & 0xFF);
    let twice = ((result & 0xFF) << 16) | (result & 0xFF00) | ((result >> 16) & 0xFF);
    let ok = result == c % 256 * 65_536 + c / 256 % 256 * 256 + c / 65_536 % 256
        && result <= 0xFF_FFFF
        && twice == c % 16_777_216;
    let z = ok as u8;
    z - 1 + 1
}
