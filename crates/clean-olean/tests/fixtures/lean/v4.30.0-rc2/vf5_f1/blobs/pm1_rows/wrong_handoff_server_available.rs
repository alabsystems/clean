#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_handoff_server_available.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.
#![allow(arithmetic_overflow)]

/// `handoff_server_available`'s clause claiming a server: false at the one input.
pub fn handoff_server_available_wrong() -> u8 {
    let result = false;
    let ok = result;
    let z = ok as u8;
    z - 1 + 1
}
