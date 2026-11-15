#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_separates.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `separates`'s clause dividing the chip right after the active one: false at (1, 0).
pub fn separates_wrong(index: usize, active: usize) -> u8 {
    let result = index > 0 && index != active && index - 1 != active;
    let ok = result
        == (if index == 0 {
            false
        } else if index <= active {
            index < active
        } else {
            index - 1 >= active
        });
    let z = ok as u8;
    z - 1 + 1
}
