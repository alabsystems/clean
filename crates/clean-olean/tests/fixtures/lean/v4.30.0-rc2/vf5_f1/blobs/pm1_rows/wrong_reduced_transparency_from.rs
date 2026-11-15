#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_reduced_transparency_from.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `reduced_transparency_from`'s clause as a conjunction: false at (true, true).
pub fn reduced_transparency_from_wrong(high_contrast: bool, transparency_effects: bool) -> u8 {
    let result = high_contrast || !transparency_effects;
    let ok = result == (high_contrast as u8 + !transparency_effects as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
