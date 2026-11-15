#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/amacs/src/protocol/anchor.rs `H6_SHIFT`, `h6_of_hash`
const H6_SHIFT: u32 = 40;
pub const fn h6_of_hash(hash: u64) -> u64 {
    hash >> H6_SHIFT
}
/// amacs SPECS.md: `ensures result == (hash / 1099511627776)` and `ensures result <= 16777215`.
pub fn h6_of_hash_spec(hash: u64) -> u8 {
    let result = hash >> H6_SHIFT;
    let ok = result == hash / 1099511627776 && result <= 16777215;
    let z = ok as u8;
    z - 1 + 1
}
