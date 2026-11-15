#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_boot_health.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum BootHealthLane {
    FullProof,
    CountOnly,
}
/// The clause with `a < 1`: false at (true, 1).
pub fn boot_health_lane_wrong(handoff_target: bool, attempts_after_launch: u32) -> u8 {
    let result = if handoff_target && attempts_after_launch <= 1 {
        BootHealthLane::CountOnly
    } else {
        BootHealthLane::FullProof
    };
    let ok = {
        let count_only = matches!(result, BootHealthLane::CountOnly);
        count_only == (handoff_target && attempts_after_launch < 1)
    };
    let z = ok as u8;
    z - 1 + 1
}
