#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_full_follow_due.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `full_follow_due`'s clause letting the phase step by two: false at (false, 0, 0, 0, 2).
pub fn full_follow_due_wrong(
    timed_out: bool,
    full_before: u64,
    full_now: u64,
    phase_before: u64,
    phase_now: u64,
) -> u8 {
    let result = timed_out
        || full_before != full_now
        || phase_now < phase_before
        || phase_now - phase_before > 1;
    let jump = if phase_now == phase_before {
        false
    } else if phase_before < u64::MAX && phase_now == phase_before + 1 {
        false
    } else {
        !(phase_before < u64::MAX - 1 && phase_now == phase_before + 2)
    };
    let ok = result == (timed_out as u8 + (full_before != full_now) as u8 + jump as u8 >= 1);
    let z = ok as u8;
    z - 1 + 1
}
