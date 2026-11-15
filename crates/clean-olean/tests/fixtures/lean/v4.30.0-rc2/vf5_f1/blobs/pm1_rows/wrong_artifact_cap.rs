#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_artifact_cap.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

const ARTIFACT_CAP: u64 = 8u64 << 30;

/// `artifact_cap`'s clause as min(s, ARTIFACT_CAP) alone: false at 0.
pub fn artifact_cap_wrong(size: u64) -> u8 {
    let result = if size == 0 || size > ARTIFACT_CAP {
        ARTIFACT_CAP
    } else {
        size
    };
    let ok = if size <= 8_589_934_592 {
        result == size
    } else {
        result == 8_589_934_592
    };
    let z = ok as u8;
    z - 1 + 1
}
