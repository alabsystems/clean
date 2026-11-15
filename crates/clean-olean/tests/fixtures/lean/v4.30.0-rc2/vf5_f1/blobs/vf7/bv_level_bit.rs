#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/amacs/src/language/rust.rs `level_bit`
pub const fn level_bit(depth: u16) -> u32 {
    if depth < 32 {
        1u32 << depth
    } else {
        0
    }
}
/// PLAN-tests-to-specs F1-ready row 2 (amacs SPECS.md: a refused form, no clause): result = if depth < 32 {2^depth} else {0}, spelled: past 31 the
/// result is 0; below, it is a power of two (`r & (r - 1) == 0`) whose bit is `depth`.
pub fn level_bit_spec(depth: u16) -> u8 {
    let result = if depth < 32 { 1u32 << depth } else { 0 };
    let ok = if depth < 32 {
        result != 0 && result & (result - 1) == 0 && result >> depth == 1
    } else {
        result == 0
    };
    let z = ok as u8;
    z - 1 + 1
}
