#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_takes_part.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `takes_part`'s clause excluding every headless launch: false at (true, false).
pub fn takes_part_wrong(headless: bool, installed_keeper: bool) -> u8 {
    let result = !(headless && installed_keeper);
    let ok = result == (headless as u8 == 0);
    let z = ok as u8;
    z - 1 + 1
}
