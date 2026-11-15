#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_er_pack_high.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const US_MASK: u64 = (1 << 48) - 1;

/// `pack`'s high conjunct with a 17-bit session half: false at session 2^16.
pub fn er_pack_high_wrong(session: u64, now_us: u64) -> u8 {
    let result = ((session & 0xFFFF) << 48) | (now_us & US_MASK);
    let ok = result / 281_474_976_710_656 == session % 131_072;
    let z = ok as u8;
    z - 1 + 1
}
