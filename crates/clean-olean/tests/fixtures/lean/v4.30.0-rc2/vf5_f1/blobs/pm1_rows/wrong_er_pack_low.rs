#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_er_pack_low.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const US_MASK: u64 = (1 << 48) - 1;

/// `pack`'s low conjunct with a 49-bit stamp half: false at us = 2^48.
pub fn er_pack_low_wrong(session: u64, now_us: u64) -> u8 {
    let result = ((session & 0xFFFF) << 48) | (now_us & US_MASK);
    let ok = result % 562_949_953_421_312 == now_us % 562_949_953_421_312;
    let z = ok as u8;
    z - 1 + 1
}
