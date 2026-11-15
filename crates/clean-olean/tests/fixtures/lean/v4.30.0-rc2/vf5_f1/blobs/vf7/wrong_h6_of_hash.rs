#![allow(dead_code)]
// A VF7 negative control (Clean docs/DECISIONS.md R206): the harness of `bv_h6_of_hash.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

const H6_SHIFT: u32 = 40;
/// `h6_of_hash`'s clause with the bound `<= 16777214` for `<= 16777215`: false at `u64::MAX`.
pub fn h6_of_hash_wrong(hash: u64) -> u8 {
    let result = hash >> H6_SHIFT;
    let ok = result == hash / 1099511627776 && result <= 16777214;
    let z = ok as u8;
    z - 1 + 1
}
