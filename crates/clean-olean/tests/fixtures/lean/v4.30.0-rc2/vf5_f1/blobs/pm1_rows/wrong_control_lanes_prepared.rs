#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_control_lanes_prepared.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `control_lanes_prepared`'s clause needing only one lane: false at (1, 0).
pub fn control_lanes_prepared_wrong(rpc: usize, subscriptions: usize) -> u8 {
    let result = rpc > 0 && subscriptions > 0;
    let ok = if rpc == 0 && subscriptions == 0 {
        !result
    } else {
        result
    };
    let z = ok as u8;
    z - 1 + 1
}
