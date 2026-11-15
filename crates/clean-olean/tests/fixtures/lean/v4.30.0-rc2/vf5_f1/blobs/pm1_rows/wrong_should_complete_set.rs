#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_should_complete_set.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `should_complete_set`'s clause without asked: false at (true, false, true).
pub fn should_complete_set_wrong(consented: bool, adopted: bool, asked: bool) -> u8 {
    let result = consented && (adopted || asked);
    let ok = result == (consented as u8 + adopted as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
