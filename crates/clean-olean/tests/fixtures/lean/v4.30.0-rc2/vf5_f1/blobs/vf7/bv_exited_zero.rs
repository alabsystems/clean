#![allow(dead_code)]
// VF7, first slice (Clean docs/DECISIONS.md R206): an aterm function copied VERBATIM
// from aterm (`7543390498`; the `// aterm:` line names the source) and its SPEC
// HARNESS: the same body, then the crate's SPECS.md clause written apart from the
// body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly when the clause is
// false, so "the harness never panics" is "the clause holds for every input".

// aterm: crates/aterm-keeper/src/core.rs `exited_zero`
pub const fn exited_zero(status: i32) -> bool {
    status & 0x7f == 0 && (status >> 8) & 0xff == 0
}
/// aterm-keeper SPECS.md: exited_zero(s) ⇔ s & 0x7f = 0 ∧ (s >> 8) & 0xff = 0, the
/// two fields read arithmetically on the status's bits (`s as u32`).
pub fn exited_zero_spec(status: i32) -> u8 {
    let result = status & 0x7f == 0 && (status >> 8) & 0xff == 0;
    let u = status as u32;
    let ok = result == (u % 128 == 0 && (u / 256) % 256 == 0);
    let z = ok as u8;
    z - 1 + 1
}
