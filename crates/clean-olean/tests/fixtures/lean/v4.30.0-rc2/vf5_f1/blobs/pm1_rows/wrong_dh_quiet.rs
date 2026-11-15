#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_dh_quiet.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `quiet`'s clause without presence: false at (true, false, false, true, false).
pub fn dh_quiet_wrong(
    focused: bool,
    input_within_quiet: bool,
    input_within_presence: bool,
    settled: bool,
    handoff_busy: bool,
) -> u8 {
    let result =
        focused && !input_within_quiet && input_within_presence && settled && !handoff_busy;
    let ok = result
        == (focused as u8 + !input_within_quiet as u8 + settled as u8 + !handoff_busy as u8 == 4);
    let z = ok as u8;
    z - 1 + 1
}
