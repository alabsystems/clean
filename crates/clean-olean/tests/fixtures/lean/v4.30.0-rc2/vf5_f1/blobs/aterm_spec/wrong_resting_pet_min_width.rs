#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_resting_pet_min_width.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `resting_pet_min_width`'s clause as 2w: false at 0.
pub fn resting_pet_min_width_wrong(cell_w: usize) -> u8 {
    if cell_w > (usize::MAX - 1) / 2 {
        return 1;
    }
    let result = cell_w * 2 + 1;
    let ok = result == cell_w + cell_w;
    let z = ok as u8;
    z - 1 + 1
}
