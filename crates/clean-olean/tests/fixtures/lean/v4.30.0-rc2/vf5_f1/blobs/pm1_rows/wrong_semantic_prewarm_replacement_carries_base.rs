#![allow(dead_code)]
// A negative control (Clean docs/DECISIONS.md R206's form): the harness of
// `bv_semantic_prewarm_replacement_carries_base.rs`, the same body, with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

/// `semantic_prewarm_replacement_carries_base`'s clause as exclusive or: false at (true, true).
pub fn semantic_prewarm_replacement_carries_base_wrong(
    new_has_base: bool,
    replaced_has_base: bool,
) -> u8 {
    let result = new_has_base || replaced_has_base;
    let ok = result == (new_has_base as u8 + replaced_has_base as u8 == 1);
    let z = ok as u8;
    z - 1 + 1
}
