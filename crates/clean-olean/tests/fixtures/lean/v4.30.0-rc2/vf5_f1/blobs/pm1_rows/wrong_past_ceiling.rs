#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_past_ceiling.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

mod handoff_carry {
    pub(crate) const MAX_TURN_ID: u64 = i64::MAX as u64;
}

/// `past_ceiling`'s clause with no top: false at m = u64::MAX, c = MAX_TURN_ID.
pub fn past_ceiling_wrong(minted: u64, ceiling: u64) -> u8 {
    let result = ceiling > 0 && ceiling < crate::handoff_carry::MAX_TURN_ID && minted > ceiling;
    let ok = if ceiling == 0 {
        !result
    } else {
        result == (minted > ceiling)
    };
    let z = ok as u8;
    z - 1 + 1
}
