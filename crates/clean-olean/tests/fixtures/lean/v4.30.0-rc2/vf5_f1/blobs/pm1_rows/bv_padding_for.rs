#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/atpkg/src/tarread.rs `BLOCK`, `padding_for`
const BLOCK: usize = 512;

/// Bytes of zero padding after `size` content bytes, rounding up to a block.
#[inline]
pub const fn padding_for(size: u64) -> u64 {
    let rem = size % BLOCK as u64;
    if rem == 0 {
        0
    } else {
        BLOCK as u64 - rem
    }
}
/// atpkg SPECS.md tar-denotation (the `padding_for` clause): padding_for(s) =
/// (512 - s mod 512) mod 512, spelled as what it is: the p < 512 with s mod 512 + p either 0
/// or 512 (s + p a multiple of 512). The formula itself takes a remainder of a computed
/// value, whose fresh bit decomposition F1's certificate search does not refute (measured: 2
/// of 21 obligations).
pub fn padding_for_spec(size: u64) -> u8 {
    let rem = size % BLOCK as u64;
    let result = if rem == 0 { 0 } else { BLOCK as u64 - rem };
    let ok = result < 512 && (size % 512 + result == 0 || size % 512 + result == 512);
    let z = ok as u8;
    z - 1 + 1
}
