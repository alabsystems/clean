#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_capture_flying_alpha.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `capture_flying_alpha`'s clause ignoring pet mode: false at (true, true, 1).
pub fn capture_flying_alpha_wrong(pet_mode: bool, kitty_enabled: bool, cat_alpha: u8) -> u8 {
    let result = if kitty_enabled && !pet_mode {
        cat_alpha
    } else {
        0
    };
    let ok = result == (if kitty_enabled { cat_alpha } else { 0 });
    let z = ok as u8;
    z - 1 + 1
}
