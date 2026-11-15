#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_tainted_at.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `tainted_at`'s clause tainting the deadline's own instant: false at (false, 5, 5, 0).
pub fn tainted_at_wrong(
    capture_forced: bool,
    now_ns: u64,
    taint_until_ns: u64,
    capture_depth: u64,
) -> u8 {
    let result = capture_forced || capture_depth != 0 || now_ns < taint_until_ns;
    let ok = result
        == (capture_forced as u8 + (capture_depth > 0) as u8 + (taint_until_ns >= now_ns) as u8
            >= 1);
    let z = ok as u8;
    z - 1 + 1
}
